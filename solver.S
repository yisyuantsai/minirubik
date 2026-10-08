    .equ CUBIES,         7
    .equ MOVES,          9
    .equ IDA_MAX_DEPTH, 11

    # ida_frame_t layout:
    #   +0 : uint16_t p
    #   +2 : uint16_t o
    #   +4 : uint8_t  prev_index
    #   +5 : uint8_t  next_i
    .equ FRAME_SIZE,     6


    .section .text
    .globl _start

_start:
    # Hand-written RV32I solver will start here.

1:
    j 1b


    # ------------------------------------------------------------------------
    # Read-only target data
    # ------------------------------------------------------------------------

    .section .rodata

input_state:
    .asciz "21345671111111"

allowed_moves:
    # previous face = R
    .byte 0x13, 0x14, 0x15, 0x26, 0x27, 0x28, 0, 0, 0

    # previous face = B
    .byte 0x00, 0x01, 0x02, 0x26, 0x27, 0x28, 0, 0, 0

    # previous face = D
    .byte 0x00, 0x01, 0x02, 0x13, 0x14, 0x15, 0, 0, 0

    # root
    .byte 0x00, 0x01, 0x02, 0x13, 0x14, 0x15, 0x26, 0x27, 0x28

allowed_count:
    .byte 6, 6, 6, 9


    # Host-precomputed transition and heuristic tables
    .include "tables_generated.inc"


    # ------------------------------------------------------------------------
    # Writable target data
    # ------------------------------------------------------------------------

    .section .bss
    .balign 2

ida_stack:
    .space (IDA_MAX_DEPTH + 1) * FRAME_SIZE

solution:
    .space IDA_MAX_DEPTH