sallyport_entry:
    csrci mstatus, 0x08

    li t0, 0x80000000
    csrw mtvec, t0

    li t0, 0x9B989D989D1E
    csrw pmpcfg0, t0

    jal zero, -0x21034
