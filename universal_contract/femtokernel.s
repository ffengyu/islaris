kernel:
    la      ra, adv
    csrrw   x0, pmpaddr0, ra
    li      ra, 0x0000000000010000
    csrrw   x0, pmpaddr1, ra
    li      ra, 0xf00
    csrrw   x0, pmpcfg0, ra
    la      ra, ih
    csrrw   x0, mtvec, ra
    la      ra, adv
    csrrw   x0, mepc, ra
    csrrw   x0, mstatus, x0
    mret
ih:
    auipc   ra, 0
    lw      ra, 12(ra)
    mret
adv:
    nop
