#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern void probe(uint8_t *rows);

void observe(uint64_t seed) {
    _Alignas(64) uint8_t storage[385];
    uint8_t *rows = storage + 1;
    for (unsigned i = 0; i < 384; ++i)
        rows[i] = (uint8_t)(7*i + seed + 53*(i/16));
    probe(rows);
    printf("%" PRIu64, seed);
    for (unsigned i = 0; i < 48; ++i) {
        uint64_t word;
        memcpy(&word, rows + 8*i, sizeof(word));
        printf(" %" PRIu64, word);
    }
    putchar('\n');
}
