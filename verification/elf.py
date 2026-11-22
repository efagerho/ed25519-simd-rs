"""Read linked x86-64 ELF symbols and cross-check section and load mappings."""
import os
import re
import struct
import subprocess

def require(condition, message):
    if not condition:
        raise ValueError(message)


def symbol_extent(binary, symbol):
    names = subprocess.check_output(["nm", "-S", "--defined-only", binary], text=True)
    matches = re.findall(rf"^([0-9a-fA-F]+) ([0-9a-fA-F]+) [tT] {re.escape(symbol)}$", names, re.M)
    require(len(matches) == 1, f"expected one defined {symbol} in {binary}")
    addr, size = matches[0]
    return int(addr, 16), int(size, 16)



ELF_HEADER = struct.Struct("<16sHHIQQQIHHHHHH")
PROGRAM_HEADER = struct.Struct("<IIQQQQQQ")


def load_offset(file, pc, size, *, readonly_data=False):
    """Translate one file-backed range through a PT_LOAD with the required permissions."""
    end = pc + size
    require(0 <= pc < end <= 2**64, "invalid symbol range")
    file_size = os.fstat(file.fileno()).st_size
    header = file.read(ELF_HEADER.size)
    require(len(header) == ELF_HEADER.size, "truncated ELF header")
    ident, kind, machine, _, _, phoff, _, _, _, stride, count, *_ = ELF_HEADER.unpack(header)
    require(ident[:6] == b"\x7fELF\x02\x01" and machine == 62 and kind in (2, 3),
            "requires a linked little-endian x86-64 ELF")
    require(stride >= PROGRAM_HEADER.size and phoff + count * stride <= file_size,
            "invalid ELF program header table")
    offset = None
    for index in range(count):
        file.seek(phoff + index * stride)
        tag, flags, pos, addr, _, filesz, memsz, _ = PROGRAM_HEADER.unpack(file.read(PROGRAM_HEADER.size))
        if tag != 1:  # PT_LOAD
            continue
        require(filesz <= memsz and pos + filesz <= file_size and addr + memsz <= 2**64,
                "invalid PT_LOAD extent")
        if not memsz or addr >= end or pc >= addr + memsz:
            continue
        permissions = (flags & 4 and not flags & 2) if readonly_data else (flags & 1)
        require(offset is None and permissions and addr <= pc and end <= addr + filesz,
                "range needs one file-backed PT_LOAD with the required permissions")
        offset = pos + pc - addr
    require(offset is not None, "symbol outside loadable segments")
    return offset


def executable_offset(file, pc, size):
    return load_offset(file, pc, size)


def symbol_bytes(binary, pc, size, *, readonly_data=False):
    section = ".rodata" if readonly_data else ".text"
    sections = subprocess.check_output(["objdump", "-h", "-j", section, binary], text=True)
    match = re.search(rf"^\s*\d+ {re.escape(section)}\s+(\w+)\s+(\w+)\s+\w+\s+(\w+)", sections, re.M)
    require(match, f"missing ELF {section} section")
    length, address, section_offset = (int(x, 16) for x in match.groups())
    require(address <= pc and pc + size <= address + length, f"range outside {section}")
    with open(binary, "rb") as file:
        offset = load_offset(file, pc, size, readonly_data=readonly_data)
        require(offset == section_offset + pc - address, f"{section} and PT_LOAD disagree on offset")
        file.seek(offset)
        raw = file.read(size)
    require(len(raw) == size, "truncated symbol")
    return raw
