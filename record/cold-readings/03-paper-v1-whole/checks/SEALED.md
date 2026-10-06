# SEALED predictions — sealed BEFORE measuring, with odds

Format: id · time sealed (from `date`) · prediction · odds · outcome (filled AFTER the measurement, same size of type).

## Part 1 (sealed 2026-10-05 12:18:52 CEST, after reading §1 only, before any code)

- **S1** · The rule of §1.2, implemented literally from §1 alone, equals the 2-adic Smith form of the Laplacian of Q_n for every n = 2..11 (multiset of exponents, with the one free summand). **Odds 80 %** (risks: an ambiguity or typo in §1.2 — pooling ties, shift-0 convention, small-clock exponent).
- **S2** · Theorem DW holds numerically for n = 2..11 (Syl_2 of the folded Laplacian = Syl_2 K(Q_n) with Z/2's removed and exponents lowered by one). **Odds 85 %.**
- **S3** · Control: Q_n/<x1x2> does NOT satisfy the fold law for some n in 3..11. **Odds 95 %** (the paper says so in §1.3; I expect it fails already at n = 3 or 4).
- **S4** · Control: the rule with one digit of I dropped (my variant: drop the lowest element of I when building the dancers, keeping k, λ, multiplicities) disagrees with the Smith form for some n ≤ 8. **Odds 97 %.**
- **S5** · The examples of §1.2 (n = 6) and §1.3 (n = 5, folded) are reproduced exactly by the Smith form. **Odds 92 %.**
- **S6** · The "equivalent form" of §1.2 (u_i(D) = k + K + κ(m,K) + x_D for i ≥ 1) holds identically for every family λ ≤ 200 and shift 1 ≤ i ≤ 60. **Odds 75 %** (it is stated as Proposition 5.3; sign/index typos are common in such identities).
- **S7** · Lemma 7.9 claim: the integer antitonic fit is non-increasing for every (λ, i) that occurs in Q_n, n ≤ 64. **Odds 85 %.**
- **S8** · Corollary 1.5: all big clocks are ≥ 1 (no trivial factor Z/2^0 hides in the count), for every n ≤ 64. **Odds 90 %.**

### Outcomes of S1–S8 (written 2026-10-05 12:24:50 CEST, after the measurements)

| id | odds | outcome | evidence |
|---|---|---|---|
| S1 | 80 % | **HIT** — rule == Smith form for every n = 1..12 (one more than sealed) | logs/check31_*.log |
| S2 | 85 % | **HIT** — DW holds for n = 1..12 | same |
| S3 | 95 % | **HIT** — Q_n/<x1x2> violates the fold law at every n = 3..12 (n = 2 coincides) | same |
| S4 | 97 % | **HIT** — drop-lowest-digit rule fails at n = 2 and 4..12 | same |
| S5 | 92 % | **HIT** — both examples exact, intermediate raw clocks too | logs/example_n6.log |
| S6 | 75 % | **HIT** — 363 600 (λ,i,D), 0 mismatches (λ ≤ 300, i ≤ 100) | logs/rule_internal_300_100_300.log |
| S7 | 85 % | **HIT** — 22 650 (λ,i) with λ+2i ≤ 300, fit always non-increasing | same |
| S8 | 90 % | **HIT** — no big clock < 1 for λ+2i ≤ 300 | same |

No failure among S1–S8. Calibration note: 8 hits out of 8 at stated odds 75–97 % — my odds were somewhat low.
## Part 2 (sealed 2026-10-05 12:35:19 CEST)

- **S9** · The integer part of Lemma 7.2(b) is false as stated: for x = (3,4,3,4), b = 2, δ = (1,1,0,0) the integer fit of x+δ differs from the integer fit of x plus δ (as multisets). **Odds 95 %** (my hand computation).
- **S9 outcome** (2026-10-05 12:35:42 CEST): HIT — intfit(x+δ) = (5,4,4,3) ≠ (5,5,3,3) = intfit(x)+δ; control equal.
- **S10** · Nonetheless, in the cells that occur (the shifts used in §7.4), the bad configuration never arises: whenever Lemma 7.2(b) is applied, no level set of fit(x) of non-integer value straddles a cut where δ jumps. I will test the CONSEQUENCE that matters: Smith(M) = αK + κ + ŷ (Theorem 6.5's conclusion) for all cells with λ ≤ 127, i ≤ 40, α ∈ {1,2}. **Odds 90 %.**
- **S11** (sealed 2026-10-05 12:38:38 CEST) · In all houses H = (I,k,ℓ,α), k ≤ 7, α ∈ {1,2}: NO level set of fit(x_{H'}) of non-integer value straddles a jump of d_1 (Theorem F step 1), and NO level set of fit(x_H) of non-integer value straddles the boundary b of J_H or its mirror (Theorem 7.10 (U2)). Equivalently the integer-shift claims hold there. **Odds 80 %** (the theorem is numerically right for n ≤ 12, so something must prevent it; but it could also be that straddling happens with integer values only, or happens and is compensated).
- **S12** · The construction of V in the proof of Theorem F, implemented literally, yields (E), (M), (G) in every house k ≤ 7, α ∈ {1,2}. **Odds 88 %.**
- **S13** · Smith(M^{(α)}(λ,i)) from the closed form of Theorem 4.4 equals αK + κ(m,K) + ŷ (i ≥ 1) and ∞ + αK + ŷ♯ (i = 0) for all λ ≤ 127, 0 ≤ i ≤ 30, α ∈ {1,2}. **Odds 90 %.**
- **S14** · The direct Smith form of σ^{(α)}_i on the lattice T(λ) built from §3 equals the small clocks ⊕ coker(2^k M) for λ ≤ 31, i ≤ 10, α ∈ {1,2}. **Odds 90 %.**
- **S15** · Theorem O: brute-force count of golden bijections L_r → F_r is exactly 1 for all s ≤ 5, 0 ≤ r ≤ 2^s; the control (golden = clear ANY all-ones block of consecutive bits, not only a top block) gives a count ≠ 1 for some (s, r). **Odds 97 % / 85 %.**
- **S11 outcome** (2026-10-05 12:41:15 CEST): **HIT** — 43 690 houses (k ≤ 7, α ∈ {1,2}), 20 052 jumps of d_1 examined: 0 straddles of ANY value; 0 straddles at the cut b and its mirror; 0 for the penalty shifts P ≤ 6 and the i = 0 deletion. (logs/theoremF_k7.log)
- **S12 outcome** (2026-10-05 12:41:15 CEST): **HIT** — the literal construction gives (E), (M), (G) in all 43 690 houses; 0 failures of any kind. Controls detected: c_F − 1 in 2 550 of 3 979 flat cases, «no flat fix» in 2 808 of 3 979.
- **S13 outcome** (2026-10-05 12:49:59 CEST): **HIT** — 7 874 cells (λ ≤ 127, 0 ≤ i ≤ 30, α ∈ {1,2}): Smith(M) from the closed form = Theorem 7.10 prediction in every cell; 338 582 entries have exactly the cost-form valuation; 1 093 deficit-law coefficients correct; control (raw clocks) rejected in all 1 876 pooling cells. (logs/cells_smith_127_30.log)
- **S14 outcome** (2026-10-05 12:49:59 CEST): **HIT** — direct Smith form of σ^{(α)}_i on T(λ) built from §3: 639 cells (λ ≤ 31, i ≤ 10) + 762 cells (λ ≤ 63, i ≤ 8), 0 mismatches; 43 + 372 cells SKIPPED (predicted exponent ≥ 60, beyond mod 2^64), counted; control rejected in all 102 + 172 pooling cells. For α = 1 the prediction equals rule.X. (logs/family_lattice_31_10.log, logs/family_lattice_63_8.log)
- **S15 outcome** (2026-10-05 12:49:59 CEST): **HIT / HIT** — count of golden bijections = 1 for all 69 pairs (s ≤ 5, 0 ≤ r ≤ 2^s); controls «any run» and «any subset» give counts ≠ 1 in 26 and 42 pairs; bit description = (γ = 0) on 5 461 arrows. (logs/theoremO_brute.log)
## Part 2b — §10 machine checks (sealed 2026-10-05 13:02:05 CEST)

- **S16** · Family-level fold law, end-to-end from the definition X̄(λ,i) = T(λ)/(τ_i T + (a−1)T) with a = (−1)^{D+i} exp F (divided powers built from Prop. 3.1(b) and the coproduct): X̄(λ,i) ≅ 2X(λ,i) for all λ ≤ 63, i ≤ 8 that fit mod 2^64. **Odds 92 %.** Control: replacing a by −a must fail somewhere. **Odds 95 %.**
- **S17** · The formal dance of Ψ_j on T(l), run as explicit block eliminations: every move clean (pivot invertible mod 2, Schur complement ≡ 0 mod 2) and the final matrix has the support, the entry valuations and the Smith form of M^{(2)}(l, ⌈j/2⌉), for l ≤ 31, 0 ≤ j ≤ 7. **Odds 85 %.**
- **S18** · Remark (2) of §10.5: with floor-dependent odd units on F (Ξ = 4(D+c) + u(D)F) cleanliness fails for some l ≤ 31, and not for l < 31 with my choice of units. **Odds 50 %** for "first at exactly l = 31" (depends on the units chosen); **odds 80 %** that it fails for SOME l ≤ 31.
- **S16 outcome** (2026-10-05 13:10:37 CEST): **HIT / HIT** — X̄(λ,i) ≅ 2X(λ,i) from the definition in all 513 cells (λ ≤ 63, i ≤ 8; 54 skipped, exponent ≥ 60); control −a detected in all 513. Self-checks (F^(1) = F, r!F^(r) = F^r for r ≤ 6, a^2 = 1, aτ = τa) all passed. (logs/fold_family_63_8.log)
- **S17 outcome** (2026-10-05 13:10:37 CEST): **HIT** — l ≤ 31, 0 ≤ j ≤ 7: 256 dances of Ψ_j clean; final matrix has the support and entry valuations of M^(2)(l,⌈j/2⌉) in all 256, same Smith form (224 with c ≥ 1; 32 with c = 0, row ∅ zero); dance of Σ_c reproduces M^(2)(l,c) of Thm 4.4 exactly (256/256); Bernoulli expansion of §10.2 exact (256/256). (logs/dance10_31_7.log)
- **S18 outcome** (2026-10-05 13:10:37 CEST): **FAILURE (both parts)** — with floor-dependent odd units on F (and, separately, generic payments 4q_d), Ξ = payment + u(D)F + Σ_{m≥2} η_m F^(m) stays CLEAN for every l tested (3, 5, 6, 7, 15, 23, 27, 29, 30, 31, 63), 12–50 random choices each, 20-bit and 200-bit randomness. My engine does detect both failure modes (α = 1: pivot not invertible; floor-parity F^(2): Schur ≢ 0 mod 2). My first version of this control was itself defective (payment systems are always clean — see REPORT §8). (logs/dance10_controls*.log)
## Part 3 (sealed 2026-10-05 13:11:58 CEST)

- **S19** · Corollary 1.4, odd part: for p = 3, 5, 7 and n = 2..11, Syl_p of the folded Laplacian's cokernel = Syl_p ⊕_{j even ≥ 2} (Z/2j)^{C(n,j)}. **Odds 95 %.** Control: the same formula with all j (not only even) must fail. **Odds 97 %.**
- **S20** · §11 Q2 (turned lid): Syl_2 K(Q_a □ C_b) ≅ Syl_2 K(Q_b □ C_a) for all a, b ≥ 1, a + b = n ≤ 12. **Odds 85 %.**
- **S21** · 2·Syl_2 K(Q_n) ≅ Syl_2 K(Q_a □ C_b) fails for every 1 ≤ b < n (n = 3..12), holds for b = n. **Odds 85 %.**
- **S19 outcome** (2026-10-05 13:14:02 CEST): **HIT / HIT** — odd part of Cor. 1.4 exact for n = 2..11, p = 3, 5, 7 (30/30); control «all j» differs in 21/30. p-adic engine controlled (sympy on ≤ 16×16 Laplacians, Bai's odd part n ≤ 9, negative control). (logs/check_part3.log, logs/test_smithp.log)
- **S20 outcome** (2026-10-05 13:14:02 CEST): **HIT** — Syl_2 K(Q_a □ C_b) ≅ Syl_2 K(Q_b □ C_a) for all a, b ≥ 1, a + b = n, n = 3..12.
- **S21 outcome** (2026-10-05 13:14:02 CEST): **HIT** — 2·Syl_2 K(Q_n) equals Syl_2 K(Q_a □ C_b) only for b = n, every n = 3..12.
- **S22** (sealed 2026-10-05 13:17:01 CEST) · Larsen's fusion graph of V^{⊗2} [Lar24, §2] (arrow n→n+1 label 1; arrows label 2 from n to n+1−2^i, 0 ≤ i ≤ r, 2^r ∥ n+1, no arrows into 0) gives the multiplicity of T(2n) in V^{⊗2k} equal to m_{2n}(2k) of the recursion of §1.2, for all 2k ≤ 64. **Odds 90 %.** Control: dropping the omission rule (allowing arrows into 0) must fail. **Odds 90 %.**
- **S22 outcome** (2026-10-05 13:17:10 CEST): **HIT / HIT** — 32/32 even n ≤ 64 equal; control differs 32/32; Larsen's [7] is TW21 with the same bibliographic data. (logs/larsen_check.log)
