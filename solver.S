    .equ CUBIES,         7
    .equ MOVES,          9
    .equ IDA_MAX_DEPTH, 11

    # ida_frame_t layout:
    #   +0 : uint16_t p
    #   +2 : uint16_t o
    #   +4 : uint8_t  prev_index
    #   +5 : uint8_t  next_i
    .equ FRAME_SIZE,     6


# ===========================================================================
# Text section
# ===========================================================================

    .section .text
    .globl _start


# ---------------------------------------------------------------------------
# _start
#
# Current Stage 4.4 test flow:
#
#   input_state
#       |
#       v
#   parse_and_rank
#       |
#       | a0 = p
#       | a1 = o
#       v
#   heuristic_lookup
#       |
#       | a2 = h(p,o)
#       v
#   heuristic_done
#
# The final self-loop is temporary and allows the registers to be inspected
# in Ripes.
# ---------------------------------------------------------------------------

_start:
    jal     ra, parse_and_rank

    # Invalid input?
    li      t0, -1
    beq     a0, t0, input_invalid

    # Input:
    #   a0 = permutation rank p
    #   a1 = orientation rank o
    #
    # Output:
    #   a2 = heuristic h(p,o)
    jal     ra, heuristic_lookup

heuristic_done:
    j       heuristic_done


input_invalid:
    li      a2, -1
    j       heuristic_done


# ===========================================================================
# parse_and_rank
#
# Output:
#   a0 = permutation rank [0, 5039]
#   a1 = orientation rank [0, 728]
#
# Invalid input:
#   a0 = -1
#   a1 = 0
# ===========================================================================

parse_and_rank:

    # -----------------------------------------------------------------------
    # Parse permutation digits.
    #
    # Input characters '1'..'7' are converted to internal values 0..6.
    #
    # t5 is a 7-bit used-value mask. This checks permutation uniqueness
    # without a nested comparison loop.
    # -----------------------------------------------------------------------

    la      t0, input_state
    la      t1, state_p

    li      t2, 0                  # i
    li      t5, 0                  # used-value bit mask


parse_perm_loop:
    li      t6, CUBIES
    bgeu    t2, t6, parse_ori_begin

    lbu     t3, 0(t0)

    # Convert ASCII '1'..'7' to 0..6.
    addi    t3, t3, -49

    li      t4, 7
    bgeu    t3, t4, parse_invalid

    # bit = 1 << value
    li      t6, 1
    sll     t6, t6, t3

    # Duplicate permutation value?
    and     t4, t5, t6
    bnez    t4, parse_invalid

    # Mark value as used.
    or      t5, t5, t6

    # Save parsed permutation value.
    sb      t3, 0(t1)

    addi    t0, t0, 1
    addi    t1, t1, 1
    addi    t2, t2, 1

    j       parse_perm_loop


    # -----------------------------------------------------------------------
    # Parse orientation digits.
    #
    # a1 = base-3 orientation rank
    # t5 = orientation sum modulo 3
    #
    # Only the first six orientations are included in the rank because the
    # seventh orientation is determined by the corner-twist invariant.
    # -----------------------------------------------------------------------

parse_ori_begin:
    li      t2, 0                  # i
    li      t5, 0                  # orientation sum modulo 3
    li      a1, 0                  # orientation rank


parse_ori_loop:
    li      t6, CUBIES
    bgeu    t2, t6, parse_ori_done

    lbu     t3, 0(t0)

    # Convert ASCII '1'..'3' to 0..2.
    addi    t3, t3, -49

    li      t4, 3
    bgeu    t3, t4, parse_invalid

    # ---------------------------------------------------------------
    # sum_mod3 += orientation
    #
    # Previous value is in [0,2], and orientation is in [0,2].
    # Therefore the sum is at most 4, so at most one subtraction of
    # 3 is necessary.
    # ---------------------------------------------------------------

    add     t5, t5, t3

    li      t4, 3
    bltu    t5, t4, ori_sum_ok

    addi    t5, t5, -3


ori_sum_ok:

    # The seventh orientation is not included in the base-3 rank.
    li      t4, 6
    bgeu    t2, t4, ori_skip_rank

    # ---------------------------------------------------------------
    # a1 = a1 * 3 + digit
    #
    # x * 3 = (x << 1) + x
    # ---------------------------------------------------------------

    slli    t4, a1, 1
    add     a1, t4, a1
    add     a1, a1, t3


ori_skip_rank:
    addi    t0, t0, 1
    addi    t2, t2, 1

    j       parse_ori_loop


parse_ori_done:

    # Input must contain exactly 14 characters.
    lbu     t3, 0(t0)
    bnez    t3, parse_invalid

    # Total corner orientation must be 0 modulo 3.
    bnez    t5, parse_invalid


    # -----------------------------------------------------------------------
    # Rank permutation using Lehmer code.
    #
    # Mixed-radix construction:
    #
    #   d0
    #   d0 * 6 + d1
    #   previous * 5 + d2
    #   previous * 4 + d3
    #   previous * 3 + d4
    #   previous * 2 + d5
    #
    # All constant multiplications use RV32I shifts and additions.
    # -----------------------------------------------------------------------

    la      t0, state_p

    li      t2, 0                  # i
    li      a0, 0                  # permutation rank


rank_perm_outer:

    # Only Lehmer digits d0..d5 are needed.
    # The final digit d6 is always zero.
    li      t6, 6
    bgeu    t2, t6, parse_success

    lbu     t3, 0(t0)              # current permutation value

    addi    t1, t0, 1              # pointer to entries on the right
    li      t4, 0                  # smaller = 0

    # Number of entries to the right = 6 - i.
    li      t5, 6
    sub     t5, t5, t2


rank_perm_inner:
    beqz    t5, rank_digit_done

    lbu     t6, 0(t1)

    # If right value < current value:
    #     ++smaller
    bgeu    t6, t3, rank_not_smaller
    addi    t4, t4, 1


rank_not_smaller:
    addi    t1, t1, 1
    addi    t5, t5, -1

    j       rank_perm_inner


rank_digit_done:

    # i == 0:
    # p = d0
    beqz    t2, rank_set_first

    # i == 1:
    # p = p * 6 + d1
    li      t6, 1
    beq     t2, t6, rank_mul6

    # i == 2:
    # p = p * 5 + d2
    li      t6, 2
    beq     t2, t6, rank_mul5

    # i == 3:
    # p = p * 4 + d3
    li      t6, 3
    beq     t2, t6, rank_mul4

    # i == 4:
    # p = p * 3 + d4
    li      t6, 4
    beq     t2, t6, rank_mul3

    # i == 5:
    # p = p * 2 + d5
    slli    a0, a0, 1
    add     a0, a0, t4

    j       rank_next_digit


rank_set_first:
    mv      a0, t4
    j       rank_next_digit


rank_mul6:
    # p * 6 = (p << 2) + (p << 1)
    slli    t5, a0, 2
    slli    t6, a0, 1
    add     a0, t5, t6
    add     a0, a0, t4

    j       rank_next_digit


rank_mul5:
    # p * 5 = (p << 2) + p
    slli    t5, a0, 2
    add     a0, t5, a0
    add     a0, a0, t4

    j       rank_next_digit


rank_mul4:
    # p * 4 = p << 2
    slli    a0, a0, 2
    add     a0, a0, t4

    j       rank_next_digit


rank_mul3:
    # p * 3 = (p << 1) + p
    slli    t5, a0, 1
    add     a0, t5, a0
    add     a0, a0, t4


rank_next_digit:
    addi    t0, t0, 1
    addi    t2, t2, 1

    j       rank_perm_outer


parse_success:
    ret


parse_invalid:
    li      a0, -1
    li      a1, 0
    ret


# ===========================================================================
# heuristic_lookup
#
# Input:
#   a0 = permutation rank p
#   a1 = orientation rank o
#
# Output:
#   a2 = max(perm_dist[p], ori_dist[o])
#
# Preserves:
#   a0 = p
#   a1 = o
#
# Since each heuristic entry occupies one byte, table indexing only requires
# base + index. No multiplication is required.
# ===========================================================================

heuristic_lookup:

    # hp = perm_dist[p]
    la      t0, perm_dist
    add     t0, t0, a0
    lbu     t1, 0(t0)

    # ho = ori_dist[o]
    la      t2, ori_dist
    add     t2, t2, a1
    lbu     t3, 0(t2)

    # h = max(hp, ho)
    bgeu    t1, t3, heuristic_use_perm

    # ho > hp
    mv      a2, t3
    ret


heuristic_use_perm:
    mv      a2, t1
    ret


# ===========================================================================
# Read-only target data
# ===========================================================================

    .section .rodata


# ---------------------------------------------------------------------------
# Inlined 14-character cube state
# ---------------------------------------------------------------------------

input_state:
    .asciz "21345671111111"


# ---------------------------------------------------------------------------
# Allowed moves
#
# Packed entry:
#
#   high nibble = next face
#   low nibble  = move index
#
# Previous-face indices:
#
#   0 = R
#   1 = B
#   2 = D
#   3 = root
# ---------------------------------------------------------------------------

allowed_moves:

    # previous face = R
    .byte 0x13, 0x14, 0x15
    .byte 0x26, 0x27, 0x28
    .byte 0, 0, 0

    # previous face = B
    .byte 0x00, 0x01, 0x02
    .byte 0x26, 0x27, 0x28
    .byte 0, 0, 0

    # previous face = D
    .byte 0x00, 0x01, 0x02
    .byte 0x13, 0x14, 0x15
    .byte 0, 0, 0

    # root
    .byte 0x00, 0x01, 0x02
    .byte 0x13, 0x14, 0x15
    .byte 0x26, 0x27, 0x28


allowed_count:
    .byte 6, 6, 6, 9


# ---------------------------------------------------------------------------
# Host-precomputed transition and heuristic tables
# ---------------------------------------------------------------------------

    .include "tables_generated.inc"


# ===========================================================================
# Writable target data
# ===========================================================================

    .section .bss
    .balign 2


# ---------------------------------------------------------------------------
# Explicit IDA* stack
#
# 12 frames:
#   depth 0 through depth 11
#
# 12 * 6 = 72 bytes
# ---------------------------------------------------------------------------

ida_stack:
    .space (IDA_MAX_DEPTH + 1) * FRAME_SIZE


# ---------------------------------------------------------------------------
# Optimal solution moves
#
# Maximum solution length = 11
# ---------------------------------------------------------------------------

solution:
    .space IDA_MAX_DEPTH


# ---------------------------------------------------------------------------
# Parsed permutation
#
# Seven bytes, values 0..6
# ---------------------------------------------------------------------------

state_p:
    .space CUBIES