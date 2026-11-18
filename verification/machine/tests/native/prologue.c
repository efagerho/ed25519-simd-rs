#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

extern void capture(uint64_t *out, uint64_t *a, uint64_t *b, uint64_t *registers,
                    uint64_t *status, uint64_t *frame_base);

static void initialize(uint64_t *words, size_t count, uint64_t seed, size_t first) {
    for (size_t i = 0; i < count; ++i)
        words[i] = seed + UINT64_C(0x0101010101010101) * (first + i);
}

static void print_words(const uint64_t *words, size_t count) {
    for (size_t i = 0; i < count; ++i) printf(" %" PRIu64, words[i]);
}

void observe(uint64_t seed) {
    // Space below the measured stack accommodates Linux signal delivery.
    enum { headroom = 8192, stack_words = 31 * 8, buffer_words = 4 * 8 };
    // Vary the frame's alignment modulo 64 while keeping calls SysV-aligned.
    static _Alignas(64) uint64_t backing[headroom + 6 + stack_words + 2 + 8];
    uint64_t *stack = backing + headroom + 2 * (seed % 4);
    _Alignas(64) uint64_t storage[3][buffer_words + 8];
    uint64_t registers[32 * 8], status[3];
    uint64_t *buffers[3] = {storage[0] + 1, storage[1] + 2, storage[2] + 3};

    initialize(registers, 256, seed, 0);
    initialize(stack, stack_words + 2 + 8, seed, 256);
    for (size_t r = 0; r < 3; ++r)
        initialize(buffers[r], buffer_words, seed, 504 + r * buffer_words);

    capture(buffers[0] + 8, buffers[1] + 8, buffers[2] + 8,
            registers, status, stack + 8);
    // The call writes only the return slot above the 30 modeled vector cells.
    for (size_t i = stack_words; i < stack_words + 2 + 8; ++i)
        if (i != stack_words + 1 &&
            stack[i] != seed + UINT64_C(0x0101010101010101) * (256 + i))
            __builtin_trap();
    printf("%" PRIu64, seed);
    print_words(status, 3);
    print_words(registers, 256);
    print_words(stack, stack_words);
    for (size_t r = 0; r < 3; ++r) print_words(buffers[r], buffer_words);
    putchar('\n');
}
