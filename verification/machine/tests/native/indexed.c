#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern void probe(uint8_t *rows);

void observe(uint64_t seed) {
    _Alignas(64) uint8_t rows[448];
    for (unsigned i = 0; i < sizeof(rows); ++i)
        rows[i] = (uint8_t)(7*i + seed + 53*(i/16));
    uint64_t index = 9;
    memcpy(rows + 128, &index, sizeof(index));
    probe(rows);
    printf("%" PRIu64, seed);
    for (unsigned i = 24; i < 56; ++i) {
        uint64_t word;
        memcpy(&word, rows + 8*i, sizeof(word));
        printf(" %" PRIu64, word);
    }
    putchar('\n');
}
