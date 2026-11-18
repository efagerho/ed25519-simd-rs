#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern const unsigned char probe[], probe_end[];
extern void observe(uint64_t input);

int main(int argc, char **argv) {
    if (argc == 2 && strcmp(argv[1], "--bytes") == 0) {
        size_t size = (uintptr_t)probe_end - (uintptr_t)probe;
        for (size_t i = 0; i < size; ++i) printf("%02x", probe[i]);
        putchar('\n');
        return 0;
    }
    uint64_t input;
    while (scanf("%" SCNu64, &input) == 1) observe(input);
    return ferror(stdin) ? 1 : 0;
}
