.data
    n: .word 2
    
.text
.globl __start

FUNCTION:
    # Todo: Define your own function in HW1
    # You should store the output into x10
    
    addi sp, sp, -8
    sw   x1,  4(sp)
    sw   x10, 0(sp)
    addi x9, x10, -1
    bne  x9, x0, L1
    addi x10, x0, 2
    addi sp, sp, 8
    jalr x0, 0(x1)
    
    
L1:
    srai x10, x10, 1
    jal  x1, FUNCTION
    slli x12, x10, 2
    add  x12, x12, x10
    lw   x10, 0(sp)
    lw   x1, 4(sp)
    addi sp, sp, 8
    slli x4, x10, 2
    add  x4, x4, x10
    add  x4, x4, x10
    add  x10, x12, x4
    addi x10, x10, 4
    jalr x0, 0(x1)
    

# Do NOT modify this part!!!
__start:
    la   t0, n
    lw   x10, 0(t0)
    jal  x1,FUNCTION
    la   t0, n
    sw   x10, 4(t0)
    addi a0,x0,10
    ecall