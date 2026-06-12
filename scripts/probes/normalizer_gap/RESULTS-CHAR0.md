# Char-0 incidence census — M(n) for the normalizer-gap lane (ArkLib#371)

M(n) = max over non-normalizer (b=c=0 / a=d=0 excluded), invertible (ad != bc)
hyperplanes h of #{(i,j) in (Z/n)^2 : (z^{i+j}, z^j, z^i, 1) on h}, computed by
reduction mod two split primes p == 1 (mod n), p > 2^28 (smallest such), with the
torus-action quotient (first triple point fixed to P(0,0)).  M_p(n) >= M(n);
agreement of the two primes (and of the canonical argmax (i,j)-sets) is the
char-0 signal.

| n | p1 | p2 | M_p1 | M_p2 | agree | M(n) cand | top-1 sets match | deg-flat max (valid) |
|---|----|----|------|------|-------|-----------|------------------|----------------------|
| 8 | 268435537 | 268435561 | 6 | 6 | True | 6 | True | None / None |
| 16 | 268435537 | 268435649 | 6 | 6 | True | 6 | True | None / None |
| 32 | 268435649 | 268435873 | 6 | 6 | True | 6 | True | None / None |

## n = 8
- p = 268435537 (z = 39845900): histogram over deduped non-normalizer planes through P(0,0): {3:336, 4:88, 5:20, 6:12}; rank-2 triples 42; normalizer-type skipped 42, singular skipped 1029; pass1 0.0s, recount 0.0s.
  - degenerate flats (rank-2 point sets through P00): L=8 valid=False; L=8 valid=False
  - argmax: count 6, canonical (i,j)-set [[0, 0], [1, 1], [2, 3], [3, 5], [4, 6], [6, 7]]
- p = 268435561 (z = 60851162): histogram over deduped non-normalizer planes through P(0,0): {3:336, 4:88, 5:20, 6:12}; rank-2 triples 42; normalizer-type skipped 42, singular skipped 1029; pass1 0.0s, recount 0.0s.
  - degenerate flats (rank-2 point sets through P00): L=8 valid=False; L=8 valid=False
  - argmax: count 6, canonical (i,j)-set [[0, 0], [1, 1], [2, 3], [3, 5], [4, 6], [6, 7]]

## n = 16
- p = 268435537 (z = 85424310): histogram over deduped non-normalizer planes through P(0,0): {3:11448, 4:2264, 5:100, 6:300}; rank-2 triples 210; normalizer-type skipped 210, singular skipped 10125; pass1 0.07s, recount 0.15s.
  - degenerate flats (rank-2 point sets through P00): L=16 valid=False; L=16 valid=False
  - argmax: count 6, canonical (i,j)-set [[0, 0], [1, 1], [2, 3], [4, 10], [7, 13], [14, 15]]
- p = 268435649 (z = 157800305): histogram over deduped non-normalizer planes through P(0,0): {3:11448, 4:2264, 5:100, 6:300}; rank-2 triples 210; normalizer-type skipped 210, singular skipped 10125; pass1 0.07s, recount 0.15s.
  - degenerate flats (rank-2 point sets through P00): L=16 valid=False; L=16 valid=False
  - argmax: count 6, canonical (i,j)-set [[0, 0], [1, 1], [2, 3], [4, 10], [7, 13], [14, 15]]

## n = 32
- p = 268435649 (z = 23172711): histogram over deduped non-normalizer planes through P(0,0): {3:326472, 4:28056, 5:260, 6:1932}; rank-2 triples 930; normalizer-type skipped 930, singular skipped 89373; pass1 1.5s, recount 6.66s.
  - degenerate flats (rank-2 point sets through P00): L=32 valid=False; L=32 valid=False
  - argmax: count 6, canonical (i,j)-set [[0, 0], [1, 1], [2, 3], [4, 18], [15, 29], [30, 31]]
- p = 268435873 (z = 157076058): histogram over deduped non-normalizer planes through P(0,0): {3:326472, 4:28056, 5:260, 6:1932}; rank-2 triples 930; normalizer-type skipped 930, singular skipped 89373; pass1 1.46s, recount 6.43s.
  - degenerate flats (rank-2 point sets through P00): L=32 valid=False; L=32 valid=False
  - argmax: count 6, canonical (i,j)-set [[0, 0], [1, 1], [2, 3], [4, 18], [15, 29], [30, 31]]

