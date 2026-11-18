// Decode one hex byte string per line with Intel XED in x86-64 mode.
#include <stdio.h>
#include <string.h>
#include <xed/xed-interface.h>

static void describe(const xed_decoded_inst_t *ins) {
    const xed_inst_t *form = xed_decoded_inst_inst(ins);
    printf("{\"op\":\"%s\",\"length\":%u,\"width\":%u,\"mask\":%u,"
           "\"zeroing\":%u,\"broadcast\":%u,\"evex_b\":%u,\"encoding\":%u,\"segment_override\":%u,\"operands\":[",
           xed_iclass_enum_t2str(xed_decoded_inst_get_iclass(ins)),
           xed_decoded_inst_get_length(ins), xed_decoded_inst_vector_length_bits(ins),
           xed3_operand_get_mask(ins), xed3_operand_get_zeroing(ins),
           xed_decoded_inst_is_broadcast(ins), xed3_operand_get_bcrc(ins),
           xed3_operand_get_vexvalid(ins), xed3_operand_get_seg_ovd(ins));
    int emitted = 0;
    for (unsigned i = 0; i < xed_inst_noperands(form); ++i) {
        const xed_operand_t *operand = xed_inst_operand(form, i);
        xed_operand_enum_t name = xed_operand_name(operand);
        xed_reg_enum_t reg = xed_decoded_inst_get_reg(ins, name);
        // XED exposes the EVEX mask as an operand. Its value is checked above.
        if (reg >= XED_REG_K0 && reg <= XED_REG_K7) continue;
        if (emitted++) putchar(',');
        const char *action = xed_operand_action_enum_t2str(xed_decoded_inst_operand_action(ins, i));
        printf("{\"action\":\"%s\",", action);
        if (name == XED_OPERAND_MEM0) {
            printf("\"base\":\"%s\",\"index\":\"%s\",\"disp\":%lld,\"size\":%u,\"address_width\":%u",
                   xed_reg_enum_t2str(xed_decoded_inst_get_base_reg(ins, 0)),
                   xed_reg_enum_t2str(xed_decoded_inst_get_index_reg(ins, 0)),
                   (long long)xed_decoded_inst_get_memory_displacement(ins, 0),
                   xed_decoded_inst_get_memory_operand_length(ins, 0),
                   xed_decoded_inst_get_memop_address_width(ins, 0));
        } else if (name == XED_OPERAND_IMM0) {
            printf("\"imm\":%llu", (unsigned long long)xed_decoded_inst_get_unsigned_immediate(ins));
        } else {
            printf("\"reg\":\"%s\"", xed_reg_enum_t2str(reg));
        }
        putchar('}');
    }
    puts("]}");
}

int main(void) {
    xed_tables_init();
    xed_state_t mode;
    xed_state_init2(&mode, XED_MACHINE_MODE_LONG_64, XED_ADDRESS_WIDTH_64b);
    char line[64];
    while (fgets(line, sizeof(line), stdin)) {
        size_t n = strcspn(line, "\n");
        if (n == 0 || n % 2 || n > 2 * XED_MAX_INSTRUCTION_BYTES) return 2;
        xed_uint8_t bytes[XED_MAX_INSTRUCTION_BYTES];
        for (size_t i = 0; i < n / 2; ++i)
            if (sscanf(line + 2*i, "%2hhx", &bytes[i]) != 1) return 2;
        xed_decoded_inst_t ins;
        xed_decoded_inst_zero_set_mode(&ins, &mode);
        xed_error_enum_t err = xed_decode(&ins, bytes, (unsigned)(n / 2));
        if (err == XED_ERROR_NONE) describe(&ins);
        else printf("{\"error\":\"%s\"}\n", xed_error_enum_t2str(err));
    }
    return ferror(stdin) ? 1 : 0;
}
