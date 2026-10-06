# Sealed predictions — auditor, flight 7 (Grepy Hypercube)

Sealed 2026-10-04 (time in BITACORA line «sealed S7.x»), before any run of engines_gh/gh_audit_vuelo7.py.
- S7.1 (95 %) Mode G, λ ≤ 20, i ≤ 6 (140 cells): my implementation of H-odd/H-even from the printed statements gives the same cokernel as my direct coker[τ | a−1], and both equal the rule lowered, in 140/140.
- S7.2 (90 %) control of G: sign flipped differs in ≥ 100 of 140 (the flight reports 128).
- S7.3 (95 %) Mode S sample, n = 61..100, families with half-dimension ≤ 128: 0 failures.
- S7.4 (40 %, real risk) smith_py at D = 256 takes ≤ 30 s (decides whether the half-dim-256 cells can be sampled).
- S7.5 (85 %) The flight's PB7.4 counterexample (a Borel lattice where X̄ ≠ 2X) is reproduced by the flight's own engine on a copy, same numbers.
