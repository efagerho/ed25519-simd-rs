//! Shared fixtures for native assembly tests.
use core::ffi::{c_int, c_void};

/// Eight lane-major compressed point encodings.
pub(crate) type EncodedPointChunk =
    [[u8; crate::edwards::POINT_ENCODING_LEN]; crate::batch::SIMD_LANES];

unsafe extern "C" {
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

/// A readable/writable page between inaccessible guard pages.
pub(crate) struct GuardedPage {
    mapping: *mut c_void,
    page: usize,
}

impl GuardedPage {
    pub(crate) fn new() -> Self {
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

    pub(crate) fn read_only(&self) {
        assert_eq!(unsafe { mprotect(self.middle().cast(), self.page, 1) }, 0);
    }

    pub(crate) fn buffer(&self, len: usize, end: bool) -> *mut u8 {
        assert!(len <= self.page);
        unsafe { self.middle().add(if end { self.page - len } else { 0 }) }
    }
}

impl Drop for GuardedPage {
    fn drop(&mut self) {
        assert_eq!(unsafe { munmap(self.mapping, 3 * self.page) }, 0);
    }
}
