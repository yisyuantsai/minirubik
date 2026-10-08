    .equ CUBIES,         7
    .equ MOVES,          9
    .equ IDA_MAX_DEPTH, 11

    # ida_frame_t:
    #   +0 : uint16_t p
    #   +2 : uint16_t o
    #   +4 : uint8_t  prev_index
    #   +5 : uint8_t  next_i
    .equ FRAME_SIZE,     6

    .option norelax


# ===========================================================================
# Text section
# ===========================================================================

    .section .text
    .globl _start


# ===========================================================================
# _start
# ===========================================================================

_start:
    jal     ra, parse_and_rank

    # Invalid input?
    li      t0, -1
    beq     a0, t0, solve_invalid

    # a0 = permutation rank
    # a1 = orientation rank
    jal     ra, solve_ida

    # Search failure?
    beqz    a0, solve_failed

    # Preserve solution length.
    mv      s0, a1

    # Replay the returned solution starting from the original root state.
    mv      a0, s10
    mv      a1, s11
    mv      a2, s0

    jal     ra, validate_solution

    # Keep final replayed state visible for Ripes inspection.
    mv      a3, a0
    mv      a4, a1

    # Valid solution must end at p = 0, o = 0.
    or      t0, a0, a1
    bnez    t0, validation_failed

    # Successful result.
    #
    # a0 = 1
    # a1 = optimal solution length
    # a2 = validation success
    # a3 = final permutation rank
    # a4 = final orientation rank
    li      a0, 1
    mv      a1, s0
    li      a2, 1

    j       validation_done


solve_invalid:
    li      a0, 0
    li      a1, -1
    li      a2, 0
    li      a3, 0
    li      a4, 0

    j       validation_done


solve_failed:
    li      a0, 0
    li      a1, 0
    li      a2, 0
    li      a3, 0
    li      a4, 0

    j       validation_done


validation_failed:
    li      a0, 0
    mv      a1, s0
    li      a2, 0


validation_done:
    # Ripes exit ecall.
    li      a7, 10
    ecall


# ===========================================================================
# parse_and_rank
#
# Output:
#   a0 = permutation rank [0, 5039]
#   a1 = orientation rank [0, 728]
#
# Invalid:
#   a0 = -1
#   a1 = 0
# ===========================================================================

parse_and_rank:

    # -----------------------------------------------------------------------
    # Parse permutation digits.
    #
    # ASCII '1'..'7' -> internal 0..6.
    # t5 = used-value bit mask.
    # -----------------------------------------------------------------------

    la      t0, input_state
    la      t1, state_p

    li      t2, 0
    li      t5, 0


parse_perm_loop:
    li      t6, CUBIES
    bgeu    t2, t6, parse_ori_begin

    lbu     t3, 0(t0)

    # ASCII '1'..'7' -> 0..6.
    addi    t3, t3, -49

    li      t4, 7
    bgeu    t3, t4, parse_invalid

    # bit = 1 << value
    li      t6, 1
    sll     t6, t6, t3

    # Duplicate cubie?
    and     t4, t5, t6
    bnez    t4, parse_invalid

    or      t5, t5, t6

    sb      t3, 0(t1)

    addi    t0, t0, 1
    addi    t1, t1, 1
    addi    t2, t2, 1

    j       parse_perm_loop


# ---------------------------------------------------------------------------
# Parse orientation digits.
# ---------------------------------------------------------------------------

parse_ori_begin:
    li      t2, 0
    li      t5, 0
    li      a1, 0


parse_ori_loop:
    li      t6, CUBIES
    bgeu    t2, t6, parse_ori_done

    lbu     t3, 0(t0)

    # ASCII '1'..'3' -> 0..2.
    addi    t3, t3, -49

    li      t4, 3
    bgeu    t3, t4, parse_invalid

    # Orientation sum modulo 3.
    add     t5, t5, t3

    li      t4, 3
    bltu    t5, t4, ori_sum_ok

    addi    t5, t5, -3


ori_sum_ok:
    # Only the first six orientations are explicitly ranked.
    li      t4, 6
    bgeu    t2, t4, ori_skip_rank

    # a1 = a1 * 3 + digit
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

    # Corner-twist invariant.
    bnez    t5, parse_invalid


# ---------------------------------------------------------------------------
# Rank permutation using Lehmer code.
#
# Mixed radix:
#
#   d0
#   d0 * 6 + d1
#   previous * 5 + d2
#   previous * 4 + d3
#   previous * 3 + d4
#   previous * 2 + d5
# ---------------------------------------------------------------------------

    la      t0, state_p

    li      t2, 0
    li      a0, 0


rank_perm_outer:
    li      t6, 6
    bgeu    t2, t6, parse_success

    lbu     t3, 0(t0)

    addi    t1, t0, 1
    li      t4, 0

    # Number of entries to the right = 6 - i.
    li      t5, 6
    sub     t5, t5, t2


rank_perm_inner:
    beqz    t5, rank_digit_done

    lbu     t6, 0(t1)

    bgeu    t6, t3, rank_not_smaller

    addi    t4, t4, 1


rank_not_smaller:
    addi    t1, t1, 1
    addi    t5, t5, -1

    j       rank_perm_inner


rank_digit_done:
    # i = 0
    beqz    t2, rank_set_first

    # i = 1 : * 6
    li      t6, 1
    beq     t2, t6, rank_mul6

    # i = 2 : * 5
    li      t6, 2
    beq     t2, t6, rank_mul5

    # i = 3 : * 4
    li      t6, 3
    beq     t2, t6, rank_mul4

    # i = 4 : * 3
    li      t6, 4
    beq     t2, t6, rank_mul3

    # i = 5 : * 2
    slli    a0, a0, 1
    add     a0, a0, t4

    j       rank_next_digit


rank_set_first:
    mv      a0, t4

    j       rank_next_digit


rank_mul6:
    # x * 6 = (x << 2) + (x << 1)
    slli    t5, a0, 2
    slli    t6, a0, 1
    add     a0, t5, t6
    add     a0, a0, t4

    j       rank_next_digit


rank_mul5:
    # x * 5 = (x << 2) + x
    slli    t5, a0, 2
    add     a0, t5, a0
    add     a0, a0, t4

    j       rank_next_digit


rank_mul4:
    slli    a0, a0, 2
    add     a0, a0, t4

    j       rank_next_digit


rank_mul3:
    # x * 3 = (x << 1) + x
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
# solve_ida
#
# Iterative IDA* using an explicit fixed-size stack.
#
# Input:
#   a0 = root permutation rank
#   a1 = root orientation rank
#
# Output:
#   a0 = 1 if solved
#   a1 = optimal solution length
#
# Failure:
#   a0 = 0
#   a1 = 0
#
# Register usage:
#
#   s0  = current depth
#   s1  = IDA* bound
#   s2  = current explicit-stack frame pointer
#   s3  = solution base
#   s4  = allowed_moves base
#   s5  = allowed_count base
#   s6  = perm_move base
#   s7  = ori_move base
#   s8  = perm_dist base
#   s9  = ori_dist base
#   s10 = root permutation rank
#   s11 = root orientation rank
# ===========================================================================

solve_ida:
    # Save root state.
    mv      s10, a0
    mv      s11, a1

    # Load static table addresses once.
    la      s3, solution

    la      s4, allowed_moves
    la      s5, allowed_count

    la      s6, perm_move
    la      s7, ori_move

    la      s8, perm_dist
    la      s9, ori_dist


# ---------------------------------------------------------------------------
# Initial IDA* bound:
#
# max(perm_dist[root_p], ori_dist[root_o])
# ---------------------------------------------------------------------------

    add     t0, s8, s10
    lbu     t0, 0(t0)

    add     t1, s9, s11
    lbu     t1, 0(t1)

    bgeu    t0, t1, ida_initial_perm

    mv      s1, t1
    j       ida_bound_loop


ida_initial_perm:
    mv      s1, t0


# ---------------------------------------------------------------------------
# Begin one IDA* iteration.
# ---------------------------------------------------------------------------

ida_bound_loop:
    li      t0, IDA_MAX_DEPTH
    bgtu    s1, t0, ida_fail

    # Reset depth and current frame pointer to the root frame.
    li      s0, 0
    la      s2, ida_stack

    # Root state.
    sh      s10, 0(s2)
    sh      s11, 2(s2)

    # prev_index = 3 means root.
    li      t0, 3
    sb      t0, 4(s2)

    # next_i = 0.
    sb      zero, 5(s2)


# ---------------------------------------------------------------------------
# Iterative DFS
#
# 4.8.2 refinement:
#
# s2 always points directly at the current frame.
#
# The previous implementation recomputed:
#
#   ida_stack + depth * 6
#
# on every iteration using two shifts and two adds.
# ---------------------------------------------------------------------------

ida_search_loop:

    # Current state.
    lhu     t2, 0(s2)              # current p
    lhu     t3, 2(s2)              # current o


    # Goal test.
    #
    # Solved iff p == 0 and o == 0.
    or      t4, t2, t3
    beqz    t4, ida_success


    # Enumeration state.
    lbu     t4, 4(s2)              # prev_index
    lbu     t5, 5(s2)              # next_i


    # count = allowed_count[prev_index]
    add     t6, s5, t4
    lbu     t6, 0(t6)

    # All legal children explored?
    bgeu    t5, t6, ida_backtrack


    # -----------------------------------------------------------------------
    # entry = allowed_moves[prev_index][next_i]
    #
    # Row size = 9.
    # prev * 9 = (prev << 3) + prev.
    # -----------------------------------------------------------------------

    addi    t6, t5, 1
    sb      t6, 5(s2)              # next_i++

    slli    t6, t4, 3
    add     t6, t6, t4
    add     t6, t6, t5
    add     t6, s4, t6

    lbu     a2, 0(t6)              # packed move entry

    # Low nibble = move number.
    andi    a3, a2, 0x0f

    # High nibble = next face.
    srli    a4, a2, 4


    # -----------------------------------------------------------------------
    # next_p = perm_move[current_p][move]
    #
    # Each row is 9 uint16_t entries:
    #
    #   9 * 2 = 18 bytes
    #
    # state * 18 = state * 16 + state * 2
    # -----------------------------------------------------------------------

    slli    a5, t2, 4
    slli    a6, t2, 1
    add     a5, a5, a6

    slli    a6, a3, 1
    add     a5, a5, a6

    add     a5, s6, a5

    lhu     a5, 0(a5)              # next_p


    # -----------------------------------------------------------------------
    # next_o = ori_move[current_o][move]
    # -----------------------------------------------------------------------

    slli    a6, t3, 4
    slli    a7, t3, 1
    add     a6, a6, a7

    slli    a7, a3, 1
    add     a6, a6, a7

    add     a6, s7, a6

    lhu     a6, 0(a6)              # next_o


    # next_depth = current depth + 1.
    addi    a7, s0, 1


    # -----------------------------------------------------------------------
    # next_h = max(perm_dist[next_p], ori_dist[next_o])
    # -----------------------------------------------------------------------

    add     t4, s8, a5
    lbu     t4, 0(t4)              # hp

    add     t5, s9, a6
    lbu     t5, 0(t5)              # ho

    bgeu    t4, t5, ida_h_ready

    mv      t4, t5


ida_h_ready:

    # Parent-side pruning.
    #
    # Reject child when:
    #
    #   next_depth + h > bound
    #
    add     t5, a7, t4
    bgtu    t5, s1, ida_search_loop


    # -----------------------------------------------------------------------
    # Store the chosen move.
    #
    # solution[current_depth] = move
    # -----------------------------------------------------------------------

    add     t4, s3, s0
    sb      a3, 0(t4)


    # -----------------------------------------------------------------------
    # Push child.
    #
    # Since s2 points at the current frame, pushing only requires:
    #
    #   s2 += FRAME_SIZE
    # -----------------------------------------------------------------------

    addi    s0, s0, 1
    addi    s2, s2, FRAME_SIZE

    sh      a5, 0(s2)              # child p
    sh      a6, 2(s2)              # child o
    sb      a4, 4(s2)              # child prev_index
    sb      zero, 5(s2)            # child next_i

    j       ida_search_loop


# ---------------------------------------------------------------------------
# Backtracking
# ---------------------------------------------------------------------------

ida_backtrack:
    # Root exhausted => current bound failed.
    beqz    s0, ida_bound_failed

    # Pop one explicit-stack frame.
    addi    s0, s0, -1
    addi    s2, s2, -FRAME_SIZE

    j       ida_search_loop


# ---------------------------------------------------------------------------
# No solution under the current bound.
# ---------------------------------------------------------------------------

ida_bound_failed:
    addi    s1, s1, 1

    j       ida_bound_loop


# ---------------------------------------------------------------------------
# Solution found.
#
# s0 equals the depth of the solved frame and therefore the solution length.
# ---------------------------------------------------------------------------

ida_success:
    li      a0, 1
    mv      a1, s0
    ret


# ---------------------------------------------------------------------------
# No solution within diameter 11.
# ---------------------------------------------------------------------------

ida_fail:
    li      a0, 0
    li      a1, 0
    ret


# ===========================================================================
# validate_solution
#
# Replay solution[] from the original root state using the same precomputed
# transition tables used by IDA*.
#
# Input:
#   a0 = root permutation rank
#   a1 = root orientation rank
#   a2 = solution length
#
# Output:
#   a0 = final permutation rank
#   a1 = final orientation rank
#
# Correct solver output must return:
#   a0 = 0
#   a1 = 0
# ===========================================================================

validate_solution:
    la      t0, solution
    la      t1, perm_move
    la      t2, ori_move

    li      t3, 0


validate_solution_loop:
    bgeu    t3, a2, validate_solution_done

    # move = solution[i]
    add     t4, t0, t3
    lbu     t4, 0(t4)


    # -----------------------------------------------------------------------
    # next_p = perm_move[p][move]
    #
    # p * 18 = p * 16 + p * 2
    # -----------------------------------------------------------------------

    slli    t5, a0, 4
    slli    t6, a0, 1
    add     t5, t5, t6

    slli    t6, t4, 1
    add     t5, t5, t6

    add     t5, t1, t5
    lhu     a3, 0(t5)


    # -----------------------------------------------------------------------
    # next_o = ori_move[o][move]
    # -----------------------------------------------------------------------

    slli    t5, a1, 4
    slli    t6, a1, 1
    add     t5, t5, t6

    slli    t6, t4, 1
    add     t5, t5, t6

    add     t5, t2, t5
    lhu     a4, 0(t5)


    # Advance replay state.
    mv      a0, a3
    mv      a1, a4

    addi    t3, t3, 1
    j       validate_solution_loop


validate_solution_done:
    ret


# ===========================================================================
# Read-only target data
# ===========================================================================

    .section .rodata


# ---------------------------------------------------------------------------
# Inlined cube state
# ---------------------------------------------------------------------------

input_state:
    .asciz "21345671111111"


# ---------------------------------------------------------------------------
# Allowed move enumeration
#
# Packed byte:
#
#   high nibble = next face index
#   low nibble  = move index
#
# Face indices:
#
#   0 = R
#   1 = B
#   2 = D
#   3 = root
# ---------------------------------------------------------------------------

allowed_moves:

    # Previous face = R.
    .byte 0x13, 0x14, 0x15
    .byte 0x26, 0x27, 0x28
    .byte 0, 0, 0

    # Previous face = B.
    .byte 0x00, 0x01, 0x02
    .byte 0x26, 0x27, 0x28
    .byte 0, 0, 0

    # Previous face = D.
    .byte 0x00, 0x01, 0x02
    .byte 0x13, 0x14, 0x15
    .byte 0, 0, 0

    # Root.
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
# 12 frames for depths 0..11.
#
# 12 * 6 = 72 bytes.
# ---------------------------------------------------------------------------

ida_stack:
    .space (IDA_MAX_DEPTH + 1) * FRAME_SIZE


# ---------------------------------------------------------------------------
# Solution move buffer
#
# Maximum optimal depth = 11.
# ---------------------------------------------------------------------------

solution:
    .space IDA_MAX_DEPTH


# ---------------------------------------------------------------------------
# Temporary parsed permutation
# ---------------------------------------------------------------------------

state_p:
    .space CUBIES