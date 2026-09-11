# Vision CICO-1, NR = 5, m = 2 over GF(2^8)

Run `vision5_left_parallel.magma` and `vision5_right_parallel.magma` in parallel with Magma, and wait until both finish and generate `vision5_FL.obj` and `vision5_FR.obj`.

Then run `vision5_final_bigresultant.magma`, which reads the two intermediate files and computes the full symbolic resultant, performs root recovery, back-substitution, and verification.
