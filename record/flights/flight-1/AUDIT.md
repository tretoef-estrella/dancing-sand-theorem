# Audit, first pass — Flight 1 of «Grepy el volador» (Grepy Hypercube, 3 Oct 2026)

Delivery copied with md5 into `reports/VOLADOR_1/ENTREGA_VUELO_1/`: `REPORT.md` 8195af7c26f94d07cc80f38c82aa63db · `checks/SEALED.md` c2e2c7bf5dce5e9a3a7b269190fb2adb · `DIARY.md` d72cfd497155dee98bf4959eab526b36 · `engines/rule.py` dd7f15543cbe1c7e9906d1ecb286f8ac.

## 1. Independent check of the closed rule (Conjecture W), own code — MEASURED, 15/15
`engines_gh/gh_audit_vuelo1.py`, log `logs/gh_audit_vuelo1.log` (VIGIA-FIN-OK, 21 MB, 0 s). The constructor's `rule.py` (pure combinatorics, no Smith form) against numbers produced by engines that are NOT his:
- the whole 2-part, n = 2..11 (my `gh_gates_part1.log`, two routes) and n = 12, 13 (Chaise engine `cubo_mitad.py`): 12/12 exact, one Z each;
- layers Z/2, Z/4 and «order ≥ 8» at n = 14, 15, 16 (my `aire.py` over F_2, logs `corpus4/regla299_retos/aire_1{3,4,5}_theta.log`): 3/3 exact (4032/792/3368, 8128/1820/6436, 16256/3640/12872).
- control: the rule with one big clock moved by one unit fails in 8 of 12 cells (the test can fail).

## 2. Proofs read on this pass
- Theorem Z (Bier's unimodularity, extended above the middle): Pascal induction read; block-triangular step correct on this reading. Bier's statement is known (1993); the proof and the floors above the middle are the constructor's. Not a trophy by itself.
- Theorem B (stable floors exactly for t − 1 ≤ ⌈n/2⌉): correct on this reading; explains my 40/40 + 5 extra hits.
- Theorem RT (splitting into tilting families): correct modulo cited tilting theory over Z_2 (Jantzen II.E.19–22). The step «σ is carried by any isomorphism of SL_2-modules» holds because σ = F + n − H uses only the action. Second reading owed.
- Theorem S (Steinberg families, closed form): the bidiagonal halving is correct on this reading (minors of a bidiagonal matrix are 0 or a product of entries).
- Theorem E (even family = odd family under τ(τ+2)): the 2×2 elimination is correct.
- λ = 2: correct.

## 3. Grade
- PROVED (one hand + this first pass): Z, B, S, E, λ = 2; RT modulo standard tilting theory.
- CONJECTURE: Conjecture W (small clocks P-X1 beyond the first layer, and the big-clock rule H). Measured everywhere tested, now also against independent engines.
- NOT CLOSED: the whole 2-part for every n.
- Trophies: none to register yet. Gao et al. Conj. 4.14, 5.4 and the poster's (n+1)-th factor are checked to n = 128 only THROUGH Conjecture W: conditional, not trophies.

## 4. Next
The constructor's route is the right one: prove P-R1 (odd Frobenius step with doubled payment, measured 276/276) and the even step for τ(τ+2); with Theorems E and S these give W by the two moves λ → 2λ+1, λ → λ+1. Mission 2 to a NEW constructor (hygiene, Rafa's order).
