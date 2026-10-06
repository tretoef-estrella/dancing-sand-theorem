# SEALED predictions — «Grepy el lector frío del cubo 1»
Each line written BEFORE the run it predicts; time pasted from `date`. Odds are my honest degree of belief.

## S1 — sealed Sun Oct  4 19:32:39 CEST 2026 (before any run of my engines)
- **C-G0 (engine gate).** My engine engines/mysmith.c (Z/2^64, valuation pivots) gives the same 2-adic exponents as PARI's matsnf on (a) 60 random integer matrices (sizes 4..40, entries of mixed 2-adic valuation, some singular) and (b) the Laplacian of Q_n, n = 1..7. Odds 95 %.
- **C-R0 (two forms of the rule agree).** Flight 1's form (naive staircase clocks B(μ,j) + transfers next(t) − t, PAVA by μ decreasing) and the mission's form (x_D = R_m(D) − R_{m+K}(I∖D), PAVA in o-order, plus the constant k + 2^k + κ(m, 2^k) that I derived on paper: Theorem S's clock is k + 2^k + v_2(⌈i/2^k⌉) = k + 2^k + κ(i−1, 2^k)) give the same multiset of big clocks for every λ ≤ 63 and 1 ≤ i ≤ 40, both before pooling (value by value) and after. Odds 85 % (the risk is my constant).
- **C-M0 (multiplicities).** The fusion recursion and peeling of Donkin's characters give the same m_λ(n) for n = 1..64, never a negative multiplicity. Odds 97 %.
- **C1 (check 1).** The rule as printed (flight 1 form, my code) equals Syl_2 K(Q_n) ⊕ Z computed by my engine directly on the Laplacian of Q_n for every n = 2..10. Odds 90 %. For n = 11 (if the estimate fits): 90 %; n = 12: 90 %.
- **C1-ctrl-a (no pooling).** The rule with the pooling removed differs from the direct group for at least one n ≤ 10. Odds 80 % (I do not know at which n the first pooled cell enters; if it is beyond 10 the control is run further with the tilting-free rule only against n ≤ 12 direct).
- **C1-ctrl-b (carries at m).** The rule with the column ruler read at m instead of m + K differs from the direct group for at least one n ≤ 10. Odds 90 %.
- **C1-count.** The direct groups have exactly 2^{n−1} − 1 factors of exponent ≥ 1 and exactly one entry ≡ 0 mod 2^64 (the Z), n = 2..10 (Bai). Odds 99 %.

## S2 — sealed Sun Oct  4 19:34:15 CEST 2026 (after C1 n = 2..11 held; before running n = 12, 13)
- **C1-12-13.** The rule equals the direct Laplacian Smith form at n = 12 (already sealed in S1, 90 %) and at n = 13 (new, 90 %). Memory estimate n = 13: 8192² × 8 B = 537 MB < 1.2 GB.

## S3 — sealed Sun Oct  4 19:47:54 CEST 2026 (Part 2 machine gates; before writing their code)
- **G-L34 (dance lattices, my code).** For every λ ≤ 30 and i = 0..40 (α = 1): the 2-adic Smith form of σ = F + 2(i + floor) on my own explicit lattice T_dance(λ) (built from Z by Φ and V⊗, F only) equals (a) the small clocks ⊕ 2^k·coker M with M from Theorem D's closed form (exact rationals, my own exact 2-adic Smith), and (b) the rule. Odds 95 %.
- **G-L5 (cost form).** For λ ≤ 63, 1 ≤ i ≤ 64, every D' ⊆ D: v_2(M_{DD'}) (closed form, exact) = K + κ(m, K) + R_m(D) − R_{m+K}(D') + γ(D∖D'), and every entry of M is an integer. Odds 95 %.
- **G-L6 (Theorem O by brute force).** For every I ⊆ [0, k), k ≤ 6, |I| ≤ 4, and every r: the δ-optimal perfect matching L_r → F_r (σ(D) ⊆ D) is unique and costs Σ_{L_r} ε. Odds 97 %.
- **C4 (check 4: L7 by machine, my implementation of Theorem F's construction).** For every family λ ≤ 255 with |I| ≥ 1, α = 1..4, every m_low ∈ [0, 2^k): at every level j the walk formula equals my PAVA, Cut_j and Λ_j hold, the plumber's interval is non-empty, and V_j satisfies (E), (M), (G) for c_F at both ends and at the middle of the interval; at the top the certificate v = V − P_r J, w = V − P_c J satisfies Theorem U in every real cell i = 1..4·2^k + 1 (and λ ≤ 63 also every i ≤ 300), and the i = 0 cell with the house m_low = 2^k − 1. Odds 90 % (risk: my own code, not the mathematics).
- **C4b (brute-force floor and exact Smith).** For λ ≤ 30, i = 0..64: exact min-cost r-matchings on the true valuations of M give T(r) ≥ Y(r) for every r, the exact Smith form of M equals the rule (d_r = Y(r)), and T(r) ≤ d_r. Odds 95 %.
- **C4-ctrl.** (a) With the gold removed (γ := 0) the (G) check fails in some cell; (b) with c_F := v′(I′) (a price that ignores the window) (M) or (G) fails somewhere; (c) T(r) < U(r) (unpooled partial sums) in some cell. Odds 85 %, 70 %, 95 %.
- **P-INT (integer splitting).** My example x = (1, 2, 0, 1, 2, 2) gives a non-antitonic integer split (2, 1, 2, 1, 1, 1) — 99 %; and in every base and real cell λ ≤ 255 (α = 1, i ≤ 300 for λ ≤ 63, i ≤ 4·2^k + 1 beyond) the integer fit is antitonic with ⌊μ_A⌋ ≥ ⌈μ_B⌉ for adjacent real blocks — 95 %.

## S4 — sealed Sun Oct  4 19:59:04 CEST 2026 (checks 2 and 3; before writing their code)
- **C2-table.** Bai's printed table (LAA 369 p. 260, n = 2..11, transcribed by me from the rendered PDF page, where a multiplicity 1 is printed with no superscript) equals the rule, 10/10. Odds 98 % (already equal to my direct computation by eye; the risk is my transcription).
- **C2-count.** The rule gives exactly 2^{n−1} − 1 factors for n = 1..60 (Bai Thm 1.1). Odds 99 %. (Note sealed with it: this count is automatic in the rule — each family contributes dim T(λ)/2 non-units — so it cannot test the big clocks.)
- **C2-a_n.** The number of Z/2 factors given by the rule equals Bai's generating function Σ a_{n+3}x^n = 1/((1−2x)(1−2x²)) for n = 3..60, and the closed form 2^{n−2} − 2^{⌊(n−2)/2⌋} for n = 2..60. Odds 98 %. (Also blind to the big clocks: Z/2's come only from the small clocks.)
- **C3.** The rule satisfies Gao et al. Thm 4.1 (top factor) and Thm 4.2 (2nd..(n−1)th factors) for n = 2..30. Odds 97 %. Extended to n ≤ 64 for information (same odds).
- **C3-conj.** The rule satisfies Gao et al. Conj 4.14 (n-th factor, n = 3..64), the JMM poster's (n+1)-th factor (n = 4..64) and Conj 5.4 (n = 4, 8, 16, 32, 64). Odds 90 %.
- **C3-ctrl.** I record (no prediction of direction, odds 50 %) whether the two controls of check 1 (no pooling; carries at m) violate Thm 4.1/4.2 for some n ≤ 30 — i.e. whether checks 2–3 can see the big-clock rule at all.

## S5 — sealed Sun Oct  4 20:03:50 CEST 2026 (Part 4)
- **P-LARSEN.** Larsen, arXiv:2405.16015 (2024), §2 (as quoted by the fetch tool): V^{⊗2} ⊗ T(2n) ≅ T(2n+2) ⊕ ⊕_{i=1}^{r+1} T(2n+2−2^i)^{⊕2}, 2^r ∥ n+1, omitting the T(0) terms when n = 2^r − 1. Starting from T(0) and applying this k times gives the same multiplicities as the flights' fusion recursion at n = 2k, for every n = 2k ≤ 64. Odds 93 % (risk: the fetch tool's quotation).
