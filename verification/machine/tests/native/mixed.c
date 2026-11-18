#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

extern void capture(uint64_t *cells, uint64_t *registers, uint64_t iterations,
                    uint64_t status[2]);

static uint64_t initial_word(uint64_t seed, size_t index) {
    return seed + UINT64_C(0x0101010101010101) * index;
}

void observe(uint64_t seed) {
    uint64_t registers[32 * 8], status[2];
    _Alignas(64) uint64_t storage[1 + 3 * 8];
    uint64_t *cells = storage + 1;
    for (size_t i = 0; i < 256; ++i) registers[i] = initial_word(seed, i);
    for (size_t i = 0; i < 24; ++i) cells[i] = initial_word(seed, 256 + i);

    capture(cells, registers, 1 + seed % 3, status);
    printf("%" PRIu64 " %" PRIu64 " %" PRIu64, seed, status[0], status[1]);
    for (size_t i = 0; i < 256; ++i) printf(" %" PRIu64, registers[i]);
    for (size_t i = 0; i < 24; ++i) printf(" %" PRIu64, cells[i]);
    putchar('\n');
}
