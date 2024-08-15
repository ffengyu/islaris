li t0, 0x80020000
csrw mtvec, t0

li t0, 0x989B989D981E
csrw pmpcfg0, t0
