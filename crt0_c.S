    .section .text.start
    .globl _start

_start:
    # Stack for compiler-generated C stack frames.
    li      sp, 0x00100000

    # Initialize global pointer for small-data accesses.
    .option push
    .option norelax
    la      gp, __global_pointer$
    .option pop

    call    main

    # Exit in Ripes.
    li      a7, 10
    ecall

1:
    j       1b
