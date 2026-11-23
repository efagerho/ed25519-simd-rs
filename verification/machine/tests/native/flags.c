#include <inttypes.h>
#include <stdio.h>
extern void capture(uint64_t input, uint64_t result[2]);
void observe(uint64_t input) {
    uint64_t result[2];
    capture(input, result);
    printf("%" PRIu64 " %" PRIu64 " %" PRIu64 "\n", input, result[0], result[1]);
}
