use super::*;
use core::ffi::{c_int, c_void};

core::arch::global_asm!(include_str!("abi.S"), options(raw));
unsafe extern "C" {
    fn ed25519_simd_test_scalar_abi(out: *mut u8, words: *const u8, offset: usize) -> u64;
    fn getpagesize() -> c_int;
    fn mmap(
        address: *mut c_void,
        length: usize,
        prot: c_int,
        flags: c_int,
        fd: c_int,
        offset: i64,
    ) -> *mut c_void;
    fn mprotect(address: *mut c_void, length: usize, prot: c_int) -> c_int;
    fn munmap(address: *mut c_void, length: usize) -> c_int;
}

fn operands() -> ([u8; 512], [u8; 320]) {
    let mut rng = StdRng::seed_from_u64(0x05ca_1ab1);
    let words: [[u64; LANES]; WIDE_WORDS] =
        core::array::from_fn(|_| core::array::from_fn(|_| rng.next_u64()));
    let expected = rows(WideScalar52::from_wide_words_rust(&words));
    (
        core::array::from_fn(|i| words[i / 64][i / 8 % 8].to_le_bytes()[i % 8]),
        core::array::from_fn(|i| expected[i / 64][i / 8 % 8].to_le_bytes()[i % 8]),
    )
}

#[test]
fn preserves_abi_input_and_canaries_at_every_alignment() {
    let (input, expected) = operands();
    for offset in 0..64 {
        let mut input_buffer = [0xa5; 640];
        let mut output_buffer = [0x5a; 448];
        input_buffer[offset..offset + 512].copy_from_slice(&input);
        let before = input_buffer;
        for stack_offset in [0, 16, 32, 48] {
            output_buffer.fill(0x5a);
            let code = unsafe {
                ed25519_simd_test_scalar_abi(
                    output_buffer.as_mut_ptr().add(offset),
                    input_buffer.as_ptr().add(offset),
                    stack_offset,
                )
            };
            assert_eq!(
                code, 0,
                "alignment {offset}, stack {stack_offset}, ABI check {code}"
            );
            assert_eq!(&output_buffer[offset..offset + 320], &expected);
            assert!(
                output_buffer[..offset]
                    .iter()
                    .chain(&output_buffer[offset + 320..])
                    .all(|&b| b == 0x5a)
            );
            assert_eq!(input_buffer, before);
        }
    }
}

struct Guarded {
    mapping: *mut c_void,
    page: usize,
}

impl Guarded {
    fn new() -> Self {
        unsafe {
            let page = getpagesize();
            assert!(page >= 512);
            let page = page as usize;
            // PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS: only the middle page
            // is accessible, so a stray load or store faults immediately.
            let mapping = mmap(core::ptr::null_mut(), 3 * page, 0, 0x22, -1, 0);
            assert_ne!(mapping as isize, -1);
            let region = Self { mapping, page };
            assert_eq!(mprotect(region.middle().cast(), page, 3), 0);
            region
        }
    }
    fn middle(&self) -> *mut u8 {
        unsafe { self.mapping.cast::<u8>().add(self.page) }
    }
    fn buffer(&self, len: usize, end: bool) -> *mut u8 {
        unsafe { self.middle().add(if end { self.page - len } else { 0 }) }
    }
}

impl Drop for Guarded {
    fn drop(&mut self) {
        assert_eq!(unsafe { munmap(self.mapping, 3 * self.page) }, 0);
    }
}

#[test]
fn respects_guard_pages_and_read_only_input() {
    let (input, expected) = operands();
    for input_end in [false, true] {
        for output_end in [false, true] {
            let input_region = Guarded::new();
            let output_region = Guarded::new();
            let src = input_region.buffer(512, input_end);
            let dst = output_region.buffer(320, output_end);
            unsafe {
                core::ptr::copy_nonoverlapping(input.as_ptr(), src, input.len());
                assert_eq!(
                    mprotect(input_region.middle().cast(), input_region.page, 1),
                    0
                );
                ed25519_simd_scalar_reduce_ifma(dst, src);
                assert_eq!(core::slice::from_raw_parts(dst, 320), &expected);
                assert_eq!(core::slice::from_raw_parts(src, 512), &input);
            }
        }
    }
}
