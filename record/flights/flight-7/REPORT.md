# REPORT — Mission 7, «Grepy el volador 7»: the fold law for every n

## 0. First line — does this flight prove the fold law for every n, yes or no

**NO. THIS FLIGHT DOES NOT PROVE THE FOLD LAW FOR EVERY n. IT PROVES IT FOR EVERY n ≤ 100 (the auditor had n ≤ 60), AND IT SHOWS WHAT ANY GENERAL PROOF MUST USE.**
- **Leg 0 — CLOSED.** The cell law X̄ = 2X reproduced with my own Smith form, 60/60 (λ ≤ 12, i ≤ 4); controls: without the sign of the turn it fails 53/60; on T(0) it always fails.
- **Leg A — NO CONCLUYO.** No route closed. Proved on the way: the double elements of one family are e₂X (Lemma A0), so the law is T/(τ, e₂) ≅ T/(τ, a − 1); every family is «one diagonal operator, two lattices differing by odd units» (A2.1–A2.2); half-size formulas for X̄ valid at every shift including 0 (Lemmas H-odd, H-even). Measured: the law is **not** a consequence of the symmetric functions and the fold (PA.0 FAILED, 3/813), **nor** of the Borel structure (divided powers of F and the floor) with the two natural hypotheses (PB7.4 FAILED, 24/632, after 1056/1056 with a gentle generator — Conjecture B written and struck). The safe class of perturbations was mapped (conjecture PL\*, 3 600 trials).
- **Leg B — CLOSED.** The fold law for n from the family law, with every dependency named; my half-size engine reproduces the auditor's n ≤ 60 (928 cells) in 42 s.
- **Leg C — CLOSED for n ≤ 100 by exact computation (Theorem C₇); NO CONCLUYO for every n.** Left open: flight 6's (Q)/(Q_even), or the weaker (P) for odd families and coker(1 + τ − a) ≅ coker(τ(τ + 2)/2) on T(ν) for even ones; PL\* is the measured general form.
- **Kill criterion: did not fire.** No n with X̄ ≇ 2X; 1 620 new cells (n = 61..100) all hold.
- **Failures published:** PA.0, PL.f, PL.i, PB7.2, PB7.4, PB7.5 (Conjecture B), PC7.2; errors E1 (typed times), E2 (a failed write reported as done, corrected), E3 (a number written before it was computed), E4 (a sketch first marked PROVED).

## 1. Leg 0 — calibration

**Estimate (written Sun Oct  4 12:42:31 CEST 2026, pasted from `date`, before the leg):** 5–10 % of the flight. Plan: copy `tilt_dp.py` into `engines/` (unchanged; it has no paths); write my own engine `engines/cal0.py` with my own 2-adic Smith form (exact integers modulo 2^P with minimal-valuation pivoting, all entries scaled from odd-denominator fractions); build τ_i = F + 2(D+i) and a = (−1)^(D+i) exp F on T(λ), compute X = coker τ_i and X̄ = coker[τ_i | a − 1] for every λ ≤ 12, 0 ≤ i ≤ 4 (65 cells), and check X̄ = X lowered by one (with the free Z on both sides at i = 0). Controls that can fail: X̄ = X unlowered, X̄ = X lowered by two, and the same law with a replaced by exp F (no sign). Also X against the closed rule (the auditor's rule code, used read-only as a reference). Machine: one run, < 100 MB, < 1 min.

**Run (written Sun Oct  4 12:55:37 CEST 2026, pasted):** engines/cal0.py (my own Smith form mod 2^400 with minimal-valuation pivot, my own rank over Q; lattices of engines/tilt_dp.py, copied unchanged, md5 e3d9f8ea…; the rule cell is the auditor's code, engines/gh_audit_vuelo6.py, copied with its two paths fixed to engines/), logs/cal0.log, **VIGIA-FIN-OK, 12 MB, 1 s**. Cells: λ = 1..12, i = 0..4 (60; the estimate said 65 because it counted λ = 0, which is a control here, not a cell of the law — see (d)).

| id | statement | result | control |
|---|---|---|---|
| P0.1 | X(λ, i) = coker τ_i = the rule cell, one free Z exactly at i = 0 | **held 60/60** | — |
| P0.2 | X̄(λ, i) = coker[τ_i \| a − 1] = X lowered by one, one free Z exactly at i = 0 | **held 60/60** | (a) X̄ = X unlowered: holds in 1/60 (λ = 1, i = 0, both trivial); (b) lowered by two: 2/60; (c) sign-free fold a′ = exp F: the law holds in only 7/60, fails in 53; (d) λ = 0: X̄ = X ≠ 2X at every i = 1..4 |

Examples: X(6, 2) = {1⁴, 3, 6², 10}, X̄(6, 2) = {2, 5², 9} (flight 6 §3.2); X(12, 4) = {1⁸, 2⁴, 6, 9, 13, 17}, X̄(12, 4) = {1⁴, 5, 8, 12, 16}.

**What the calibration says.** The cell law reproduces with my own Smith form. Two controls are informative and not only formal: **the sign (−1)^(D+i) is essential** (without it the law fails in 53 of 60 cells), and **the law is false on T(0) = Z** (X̄ = X there, because a = ±1 is a scalar): the fold law is a statement about families that are free over Z_2[⟨a⟩], and T(0) is not (Lemma L of flight 6 needs λ ≥ 1). Any proof must use both facts. **Leg 0 CLOSED.**

## 2. Leg A — the route

**Pre-leg notes (written Sun Oct  4 12:42:45 CEST 2026; thoughts I had while reading the material, between 12:37 and 12:42, before any Leg A estimate — said here so the estimate below is honest; grade READING until proved):**
- (n0) Flight 4b proved Conjecture W **for every α ≥ 1** (FLIGHT4 §11.0: «every λ, every α ≥ 1 and every shift i ≥ 0»). So X^(α)(T(λ), c) = coker(F + 2^α(D + c)) is known by the closed rule for every α, not only α = 1. Any route that reduces X̄ to some X^(α) of a tilting lattice is closed by the rule.
- (n1) In the eigen-frame Λ = exp(F/2)T, τ = 2J (J = D + i) and 2X ≅ 2Λ/(2Λ ∩ 2JΛ) ≅ Λ/(Λ ∩ JΛ) (multiplication by 2 is injective).
- (n2) The (n−1)-cube form of the law (note §1.3, flight 6 Theorem E): per family ν of V^⊗(n−1) at shift j, K̄ gives coker(f) and 2K gives coker(θ) on T(ν), f = 1 + τ − a, θ = τ(τ+2)/2; on the eigenline τ = 2c, f = 4⌈c/2⌉ and θ = 2c(c+1), same valuation, ratio f/θ = 1/(2⌊c/2⌋ + 1). This ratio is NOT in 𝓢 (Δ²g(0) = −2/3 is not divisible by 4), so the law is not «f = θ·unit of 𝓢».

**Leg A estimate (written Sun Oct  4 12:56:05 CEST 2026, pasted from `date`, before any Leg A pencil beyond the notes n0–n2 above):** budget 60 % of the flight; my probability of a complete pencil proof for every λ and i ≥ 1 in this flight: ~25 %. Plan: Route 1 first, but stated on cokernels only: find a statement S(N, c) about a lattice N with its divided powers that (i) is implied, for N = T(λ₁), by the fold law of the families 2λ₁+1 and 2λ₁+2, (ii) propagates through the two moves Φ and V ⊗ Φ (flight 2 A.2, B.1, C.0) using only P-R1-type eliminations (unit pivots, floor scalings), (iii) holds at the bottom N = Z. Each candidate step gated on the lattices of tilt_dp.py (λ ≤ 20) with a control that can fail, < 200 MB, < 2 min per run. If Route 1 stops (10 minutes without traction), I write where and go to Route 2 (the whole ring, R/(σ, e₂) against R/(σ, a − 1)).

### A.1 First exploration: 𝓢 and the fold are not enough (written Sun Oct  4 13:03:44 CEST 2026, pasted) — MEASURED
- **Lemma A0 (the double elements of a family; PROVED, pencil).** For λ ≥ 1 and every i: **X(λ, i)[2] = e₂·X(λ, i)**, hence **2X ≅ T/(τ, e₂)T** and the family law reads **T/(τ, e₂)T ≅ T/(τ, a − 1)T**. *Proof.* T ⊗ F₂ is free over F₂[F]/(F²) (for λ ≥ 1, T(λ) ⊗ F₂ is V ⊗ (·): T(2l+1) ⊗ F₂ ≅ V ⊗ T(l)^[1] by flight 2 A.1(c), and T(2l+2) = V ⊗ Φ(T(l)); V is free, and a tensor product with a free module over this Hopf algebra is free), so ker F̄ = im F̄ on T/2T. If 2x = τr, then F̄ r̄ = 0, so r = τr′ + 2r″; with τ² = 2τ + 2e₂ (e₂ = τ(τ − 2)/2), 2x = 2τr′ + 2e₂r′ + 2τr″, so x ≡ e₂r′ mod τT. Conversely 2e₂ = τ(τ − 2). ∎ (The note's §1.1 on one family. It fails for T(0) = Z, where F = 0 — Leg 0 control (d).)
- In the eigen-frame Λ = exp(F/2)T both ideals are diagonal: (τ, e₂) = (2J, 2J(J − 1)) and (τ, a − 1) = (2J, 2[J odd]); **on every eigenline they generate the same fractional ideal** ((2J) for J even, (2) for J odd), so the law is a statement about how the lattice Λ sits across eigenlines.
- **PA.0 FAILED (sealed 45 %; engines/s_lat.py, logs/s_lat_3000_5_3.log, VIGIA-FIN-OK, 12 MB, 50 s).** On random 𝓢-lattices (not cyclic) that are free over Z₂[a], the law holds in 810 of 813 trials and **fails in 3**: e.g. eigenvalues 4..7 with multiplicities (1, 2, 3, 2), X = {1, 1, 3, 3, 5}, X̄ = {1, 2, 2, 4} ≠ 2X = {2, 2, 4}. Control (non-free lattices): fails 1964/1964. **So 𝓢-structure + freeness do not imply the law (this sharpens flight 6's PB.1: even the full ring of symmetric functions is not enough). The proof must use the divided powers F^(m) — and, as A.4 shows later, more than them: the tilting structure.**

### A.2 Reformulations found while choosing the route (written Sun Oct  4 13:20:09 CEST 2026, pasted; pencil, PROVED unless marked)
- **(A2.1) The odd families as two lattices (PROVED, from flight 6 §3.4–3.5).** For λ = 2λ₁ + 1, N = T(λ₁), j even, c = j/2, J = D_N + c: **X̄(λ, j) ≅ coker(4J on cosh(u/2)·N)** and **2X(λ, j) ≅ coker(4J on exp(F/4)·N)**, both inside N ⊗ Q, u² = 2F_N, where 4J is the diagonal floor operator. *Proof.* π_e(exp(u/2)Φ(N)) = cosh(u/2)N + u·sinh(u/2)N (flight 6 §3.5(d)); u·sinh(u/2) = 4F·C′(F) for C = cosh(u/2) (termwise), and 4F·C′/C = u·tanh(u/2) = Σ η_m F^(m) is an integral divided-power series, so cosh(u/2)N + u sinh(u/2)N = C·(N + u tanh(u/2)N) = C·N. The second is the eigen-frame of P-R1's Σ = F + 4J (exp(−F/4)·4J·exp(F/4) = F + 4J). ∎ The two generating series are C = Σ_s F^(s)/(4^s(2s−1)!!) and E = Σ_s F^(s)/4^s: **the same series up to the odd unit (2s−1)!! in every coefficient** (flight 6 noticed this; here it is the whole odd-family question).
- **(A2.2) The even families in the (n−1)-cube form (PROVED).** For λ = ν + 1, ν = 2λ₁ + 1 odd, T(λ) = V ⊗ T(ν), and at the same shift i: **X̄(λ, i) = coker(f on T(ν)), 2X(λ, i) = coker(θ on T(ν))**, f = 1 + τ − a, θ = τ(τ + 2)/2. *Proof.* (V ⊗ M)^a ≅ M via m ↦ (1 + a)(b₀ ⊗ m) (V is the regular Z₂[C₂]-module, so V ⊗ M ≅ V ⊗ M_triv), and on that image x acts as a_M, so τ_λ becomes 1 − a + τ_ν; and coker(1 − x + τ) on Z[x]/(x²−1) ⊗ M = coker(τ(τ + 2)) on M, whose 2-multiple is coker(τ(τ+2)/2) (multiplying a matrix by 2 raises every Smith exponent by one). ∎ In the eigen-frame f = 4⌈c/2⌉, θ = 2c(c + 1) and **θ = f·h with h = (1 + τ + a)/2 = 2⌊c/2⌋ + 1**: odd on every eigenline, but h is NOT in 𝓢 (its finite differences are ±2^(r−1), one factor 2 short). So coker(θ on T) = coker(f on h·T): again two lattices, T and hT, for one diagonal operator.
- **(A2.3) In the language of 𝔾 = {1 + t(1 − g)} (READING).** The fixed group of the fold is the 1-parameter group scheme 𝔾 ≅ G_m^(2) (law t + s + 2ts); its distribution algebra is 𝓢 (D_j acts by 2^j C(c, j)), the Lie element is D₁ = τ, and a is the point t = −1 of order 2. 2X ≅ T/(D₁, D₂)T and X̄ = T/(D₁, Σ_j (−1)^j D_j)T. The quotient 𝔾/⟨a⟩ ≅ G_m^(4) by squaring is Lemma Π(b) (the fold doubles the payment). PA.0 says 𝔾-modules alone are not enough.
- **(A2.4) The Steinberg families by the dance and a determinant — ~~PROVED~~ DOWNGRADED to SKETCH (correction written Sun Oct  4 14:07:30 CEST 2026, pasted; §7 E4).** Flight 6's Theorem W̄ remains the proof for Steinberg families. For λ = 2^k − 1 the dance is a pure chain of «doblar». Ψ = Σ + P with P = Σ_{m≥2} ζ_m F^(m) strictly floor-raising by ≥ 2 has det Ψ = det Σ; each «doblar» elimination of Ψ has a unit pivot (the b₀→b₁ block is a unit series) and leaves 2·(an operator of the same shape: a unit multiple of F, floor-dependent perturbations, payment 2^(2α)(D + ⌈c/2⌉)·unit) — so at every level both sides extract the same number of units and one factor 2, and at the bottom (N = Z) the two 1×1 cokernels have the same order because the determinants agree. *The gap (found later in the leg):* the unit pivot is fine (the F-coefficient stays ≡ 1 mod 2), but «S ≡ 0 mod 2» at the next level needs the even-index coefficients to be constant mod 2, and my own count of how floor-dependence propagates (if it is divisible by 2^e at payment level α, it is divisible by 2^{min(α + 1, e − 1)} one level down) only guarantees this for about four levels. So this is a sketch, not a proof. This argument does NOT extend to |I| ≥ 1 (final matrices of size 2^|I|, where equal determinants do not fix the Smith form).
- **What this says about the route.** In every formulation the law is «one diagonal operator, two lattices that agree up to odd units»: C·N vs E·N (odd families), T vs hT (even families). PA.0 shows that agreement up to units on eigenlines is not enough in general; the units must be the specific ones (double factorials; h = 2⌊c/2⌋ + 1) and the lattices tilting.

### A.3 Which perturbations keep the cokernel (written Sun Oct  4 13:29:04 CEST 2026, pasted) — MEASURED
Engine engines/pl_test.py (logs/pl_*.log, all VIGIA-FIN-OK, ≤ 13 MB, ≤ 31 s). On N = T(l), l ≤ 12 (16 for g), c ≤ 5, five seeded trials per cell, operator A = U(D)F + 2^α(D + c)W(D) + Σ_{m≥2} ζ_m F^(m), floor functions acting on the target floor:
| variant | coefficients | α | result |
|---|---|---|---|
| a | ζ constant | 2, 3, 4 | **held 825/825** |
| b | ζ_m(floor) ≡ const mod 2 | 2, 3, 4 | **held 825/825** |
| c | ζ constant; U, W arbitrary odd floor functions | 2, 3, 4 | **held 825/825** |
| g | b and c together, l ≤ 16 | 2, 3, 4 | **held 1125/1125** |
| f | ζ_m(floor) arbitrary | 2, 3, 4, 6, 8 | **FAILED** 308/825; 104/275 at each single α (the number of cyclic factors changes) |
| e | ζ per matrix entry, ≡ const mod 2 | 2–4; 8 | **FAILED** 102/825; 26/275 at α = 8 |
| d | ζ per matrix entry, arbitrary | 2 | FAILED 197/275 (flight 6's PB.5) |
| a at α = 1 | ζ constant | 1 | FAILED 150/275 (flight 6's PB.5) |
**Conjecture (PL\*) (MEASURED, 3 600 trials, no failure).** For every tilting lattice N = T(l), every α ≥ 2 and c ≥ 1, and every operator A = Σ_{m≥0} φ_m(D)·F^(m) with floor-function coefficients such that φ₀ = 2^α(D + c)·(odd), φ₁ odd, and φ_m ≡ const mod 2 for m ≥ 2: **coker A ≅ coker(F + 2^α(D + c))**. In words: inside the Borel hyperalgebra (divided powers of F with coefficients that are functions of the floor), only the reduction mod 2 of the operator matters, and mod 2 it must be a constant-coefficient divided-power series in F. Flight 6's (P) is the constant case; the odd-family law is (P) for the series u·tanh(u/2). The failures say exactly where the line is: coefficients that are not functions of the floor (e, d), or not constant mod 2 (f), or α = 1.
**Why this matters for Route 1.** A first-order count (pencil, not a proof): conjugating or multiplying by 1 + φ(D)F^(a) changes the coefficient of F^(m) by multiples of m (through F) and of 2^(α + min(v(J), v(m))) (through the payment), so at first order the coefficient of F^(m) can be changed by anything in m·Z₂. For m odd any perturbation is removable; for m = 2 only the class mod 2 is invariant — matching (PL\*). For m = 4 first order only reaches 4·Z₂, yet b holds with ζ₄ varying by 2·(floor function): second-order terms (through ζ₂ when ζ₂ is odd) or equivalences outside the Borel algebra are needed. Equal cokernels = equivalence UAV over Z₂; U, V need not be formulas.

### A.4 ~~The law lives in the Borel hyperalgebra~~ — REFUTED: the Borel structure is NOT enough (inserted by hand between Sun Oct  4 13:35:10 and 13:35:40 CEST 2026 — the pasted times of the failed scripted write and of the diary correction; see §7 E2) — MEASURED, and a compressed form (PROVED)
- **PB7 (engines/borel_lat.py; logs/borel_lat_600.log, borel_lat_500_odd.log; VIGIA-FIN-OK, ≤ 13 MB, ≤ 102 s).** Random **Borel lattices**: graded Z₂-lattices L with integral divided powers F^(m) of degree m (no E, no tilting structure), built as Z₂⟨F⟩-spans of random homogeneous vectors with denominators 2 and 4 inside sums of shifted Weyl strings. On the 264 lattices that satisfy the two hypotheses the law needs — **L/2L free over F₂[F]/(F²)** (ker F̄ = im F̄) and L free over Z₂[a] — **the fold law held in 1056/1056 cells** (160 in the first run, 896 in the second) **and (P) at α = 2 with constant ζ held in 896/896**; on lattices outside the hypotheses (P) fails 179/1104. Compare PA.0: on 𝓢-lattices without divided powers of F the law fails. **So the law is, conjecturally, a theorem about the Borel hyperalgebra (divided powers of F and the floor), not about tilting modules.**
- **PB7.4/PB7.5 FAILED (correction written Sun Oct  4 13:40:15 CEST 2026, pasted; logs/borel_lat_400_deep.log, VIGIA-FIN-OK, 13 MB, 150 s).** With a harsher generator (strings of length up to 8, offsets 0..4, up to four generators with denominators up to 8) **the fold law FAILS on 24 of 632 cells of 158 kept Borel lattices**, and (P) fails 9/632: first failure, strings (μ, offset) = (3, 2), (7, 2), (3, 2), shift 1: X = {1³, 2², 6², 10}, **X̄ = {2, 5², 9} ≠ 2X = {1², 5², 9}** (same order). **So Conjecture B below is FALSE, and the sentence above («the law is a theorem about the Borel hyperalgebra») is withdrawn.** The 1056/1056 of the first two runs came from shallow gluing. What survives: (i) the law is not a consequence of 𝓢 and the fold (PA.0), nor of the Borel structure with the two hypotheses (PB7.4); (ii) tilting lattices carry more (the E's, i.e. both Weyl and dual-Weyl filtrations), and the proof must use it.
- ~~**Conjecture B.**~~ (REFUTED by PB7.4) For every graded Z₂⟨F⟩-lattice L with L/2L free over F₂[F]/(F²) and L free over Z₂[a], and every shift i ≥ 1: X̄(L, i) ≅ 2X(L, i). (Tilting lattices T(λ), λ ≥ 1, satisfy both hypotheses: Lemma A0 and flight 6's Lemma L.)
- **Lemma C (the compressed form; PROVED, pencil — flight 2's P-R1 for any such lattice).** Let x₁..x_r be homogeneous lifts of a basis of a complement of im F̄ in L/2L (r = rank L / 2), so {x_j, Fx_j} is a basis of L (Nakayama). Write F^(m)x_j = Σ_k α^(m)_kj x_k + β^(m)_kj Fx_k and put γ^(m) := α^(m) − 2β^(m)J (J = D + i on the x_k), an operator on W = ⊕ Z₂x_j. Then
  **X ≅ W/2MW, 2X ≅ W/MW, X̄ ≅ W/(2M, Â − 1)W**, with **M = γ^(2) − 2J(J + 1)** and **Â = Σ_{m≥0} (−1)^(J_j + m) γ^(m)** (the sign of the target floor in L).
  *Proof.* τx_j = Fx_j + 2J_j x_j is a unit pivot onto Fx_j; in L/τL, Fx_j ≡ −2J_j x_j, so τ(Fx_j) = 2F^(2)x_j + 2(J_j + 1)Fx_j ≡ 2[γ^(2) − 2J(J+1)]x_j: X ≅ W/2MW. Since τ commutes with a, (a − 1)(Fx_j) ≡ −2J_j(a − 1)x_j mod τL, so (a − 1)X is generated by the (a − 1)x_j ≡ (Â − 1)x_j. And M is the compression of e₂ = F^(2) + 2FJ + 2J(J − 1); with Lemma A0, W/(2M, M) = W/M ≅ 2X. ∎
  So the law reads **W/(2M, Â − 1) ≅ W/M**. Modulo 2, M ≡ γ^(2) and Â − 1 ≡ Σ_{s≥1} γ^(2s), a divided-power series in γ^(2) with linear term 1 (the γ^(odd) are even). If Â − 1 were M·(unit) + 2M·(·) the law would be an equality of submodules; it is not (flight 6 L(d)): the obstruction is again the divided powers (x^[2] = x²/2 is not a multiple of x).

### A.5 Two half-size formulas for X̄ (PROVED, pencil; my own derivation, used in Leg C)
- **Lemma H-odd.** λ = 2λ₁ + 1, N = T(λ₁), T = Φ(N), any shift j ≥ 0, ε = (−1)^j. Put Ch = Σ_s F^(s)/(2s−1)!!, Sh = Σ_s F^(s)/(2s+1)!! (series in F = F_N, Sh a unit). Then **X̄(λ, j) ≅ coker(τ₊ on N), τ₊ = 2(2D_N + j) + (Ch − ε)·Sh⁻¹**. *Proof.* exp(F_T)(b₀n) = b₀Ch(n) + b₁Sh(n) (flight 2 A.1(b)); with the sign of the target floor, a(b₀n) = ε[b₀Ch(n) − b₁Sh(n)]. The change of basis {b₀n, b₁n} → {b₀n, a(b₀n)} is [[1, εCh], [0, −εSh]], invertible, so T is free over Z₂[a] on b₀N. From the last formula, b₁n = b₀ChSh⁻¹n − εa(b₀Sh⁻¹n), so τ(b₀n) = b₁n + 2(2f + j)b₀n = b₀(Pn) + a·b₀(Qn) with P = ChSh⁻¹ + 2(2D_N + j), Q = −εSh⁻¹; as τ commutes with a, its matrix on (b₀N, a·b₀N) is [[P, Q], [Q, P]], and on T/(a − 1)T ≅ N it is P + Q. So X̄ = T/(τ, a − 1)T = coker(P + Q). ∎ For j even (Ch − 1)Sh⁻¹ = u·tanh(u/2), for j odd (Ch + 1)Sh⁻¹ = u·coth(u/2) (u² = 2F): flight 6's Ψ, now derived on the coinvariants, so it holds **also at j = 0** (no injectivity of τ is used).
- **Lemma H-even.** λ = ν + 1, ν odd, any shift i ≥ 0: **X̄(λ, i) ≅ coker(1 + τ_ν − a_ν on T(ν))** at the same shift i (A2.2, again on coinvariants: (V ⊗ M)/(a − 1) ≅ M and x_n ≡ a_{n−1} there). ∎
Both are square matrices of size dim T(λ)/2, against the d × 2d matrix [τ | a − 1] of the direct computation.

### A.6 Verdict of Leg A (written at the close of the leg; time in the diary line that follows)
**NO CONCLUYO.** No route closed. What happened, route by route:
- **Route 1 (the doubled payment, recursively).** The recursion of flight 2 does reach the folded operator: one «doblar» turns X̄ into the cokernel of a perturbed operator of the same shape (A2.4, A.5), with a unit pivot at every level; for the Steinberg families this gives only a sketch by determinants (A2.4, downgraded: the per-level divisibility is not controlled beyond a few levels), and at the first «paso + doblar» the final matrices have size 2^|I| and equal determinants no longer fix the Smith form. To finish one needs a perturbation-stable version of flights 3–4's Theorems O and F (the support and the exact valuations of the final matrix kept under the perturbations). The class of perturbations that is safe was measured (A.3, conjecture PL*): coefficients that are functions of the floor, constant mod 2 on F^(m), m ≥ 2, any odd units on F and on the payment, α ≥ 2. A first-order count explains m odd and m = 2 but not m = 4 (A.3). Stopped there.
- **Route 2 (the whole ring).** The law is not induced by any automorphism of X (2X is characteristic and (1 + a)X ≠ 2X), nor by a ring automorphism of Z₂[(Z/2)^m] (they are affine and f/θ = 1/h is not in the ring); it can only be an equality of Smith invariants. Not pursued further.
- **Generality tests that bound any proof.** The law is NOT a consequence of the symmetric functions and the fold (PA.0 FAILED), and NOT a consequence of the Borel structure with the two natural hypotheses (PB7.4 FAILED). A proof must use the full tilting structure (both filtrations).
**The exact statement left open (for every n):** flight 6's (Q) and (Q_even) are sufficient; the weaker statement that suffices for odd families is **(P): coker(F + 4(D + c) + Σ_{m≥2} ζ_m F^(m)) ≅ coker(F + 4(D + c)) on every T(l), for the constant ζ of u·tanh(u/2) and u·coth(u/2)**, and for even families the analogous statement for coker(1 + τ − a) against coker(τ(τ + 2)/2) on every T(ν), ν odd. Conjecture PL* (A.3) is the general form measured here.

## 3. Leg B — assembly

**Leg B estimate (written Sun Oct  4 13:42:48 CEST 2026, pasted, before the leg):** 15 % of the flight. Pencil: the fold law from the family law (flight 6 §4.2), every dependency named, and the cell-by-cell form used in Leg C (a finite set of cells per n). Machine: one engine, engines/fold_cells.py, computing X̄(λ, i) with the half-size formulas H-odd/H-even (A.5) and my own Smith form mod 2^192; gates: (G1) half-size = direct [τ | a − 1] on T(λ), λ ≤ 20, i ≤ 6, with a control that must fail (ε flipped); (G2) the fold law cell by cell for every n = 3..60 against the closed rule lowered by one (re-gating the auditor's route). Each run < 300 MB, < 10 min.

### 3.1 The fold law from the family law — PROVED, pencil (flight 6 §4.2, restated with every dependency)
**Theorem (assembly).** Fix n ≥ 1. If for every family λ of V^⊗n (λ ≡ n mod 2, m_λ(n) > 0) and i = (n − λ)/2 we have X̄(λ, i) ≅ 2X(λ, i) as Z₂-modules (with the free Z₂ at i = 0 on both sides), then **Syl₂ K̄(n) ≅ 2·Syl₂ K(Q_n)**, i.e. **Syl₂ K(Q_n) ≅ (Z/2)^{a_n} ⊕ [Syl₂ K̄(n) with every exponent raised by one]**, a_n = 2^{n−2} − 2^{⌊(n−2)/2⌋}.
*Proof.* Theorem RT (flight 1; flight 3's RT′ without tilting citations): C ⊗ Z₂ = Z₂ ⊕ Syl₂ K ≅ ⊕_λ X(λ, i)^{m_λ(n)}. Lemma RT̄ (flight 6, audited): C̄ ⊗ Z₂ = Z₂ ⊕ Syl₂ K̄ ≅ ⊕_λ X̄(λ, i)^{m_λ(n)}. Hence C̄ ⊗ Z₂ ≅ 2·(C ⊗ Z₂); cancel the one free Z₂ on each side (λ = n, i = 0; finitely generated Z₂-modules). Multiplication by 2 removes exactly the Z/2's of K, whose number is a_n (Bai; flight 6 Leg 0). ∎
**The cell form used in Leg C.** By flights 1–4 (Theorem D + Theorem F: Conjecture W in every cell), X(λ, i) is the closed rule cell. So for each n the law is equivalent to the finite check «X̄(λ, i) = rule(λ, i) lowered by one» on the cells of n, and X̄(λ, i) is computed by Lemma H-odd / H-even (§2 A.5) as the cokernel of an explicit integer matrix of size dim T(λ)/2.
**Dependencies, named:** Theorem RT/RT′ (flights 1, 3); Lemma RT̄ (flight 6); the closed rule = Conjecture W (flights 1–4: Theorems D, O, F); flight 2's construction of T(λ) over Z₂ (A.1, B.1), implemented in tilt_dp.py (flight 6, audited in the auditor's mode L); Lemmas A0, H-odd, H-even (this flight, pencil); my own exact Smith form (engines/fold_cells.py, validated by G1 and by Leg 0).

### 3.2 Gates (engines/fold_cells.py) — MEASURED
| id | what | result | control |
|---|---|---|---|
| G1 (PBG1) | half-size X̄ (H-odd/H-even) = direct coker[τ \| a − 1] on T(λ), λ ≤ 20, i ≤ 6 | **held 140/140** (logs/fold_cells_V_20_6.log, VIGIA-FIN-OK, 14 MB, 1 s) | ε flipped: differs in 128/140 |
| G2 (PBG2) | fold law cell by cell, every family of every n = 3..60 | **held: 928 cells, 0 failures** (logs/fold_cells_N_3_60.log, VIGIA-FIN-OK, 41 MB, 42 s) | — (G1's control is the one that can fail; the cell count 928 equals the auditor's) |
The auditor's n ≤ 60 is reproduced by an independent engine (half-size matrices, my Smith form) in 42 s against the auditor's 284 s for n = 49..60 alone. **Leg B CLOSED** (the assembly is pencil; the general family law it needs is NOT proved — Leg A).

## 4. Leg C — what remains

**Leg C estimate (written Sun Oct  4 13:45:03 CEST 2026, pasted, before the leg):** 15 % of the flight (the leg may take a little more because Leg A ended early without a proof). Plan: extend the PROVED range of the fold law beyond the auditor's n ≤ 60 with engines/fold_cells.py (Theorem of §3.1 + the cell check). Cost model: Smith of a half-size matrix of dimension D costs ~ D³; measured 7 s for D = 256; D = 512 first appears at n = 62 (λ = 62), D = 1024 at n = 94 (λ = 94). Target n ≤ 93 (every cell has D ≤ 512), in runs of < 10 min and < 1.2 GB each (estimate < 300 MB per run). Then write the exact statement left open.

### 4.1 The cell check beyond the auditor (engines/fold_cells.py, mode N) — PROVED for each listed n (pencil assembly §3.1 + exact finite computation)
| run | n | new cells | half-dim max | result | log (all VIGIA-FIN-OK) |
|---|---|---|---|---|---|
| gate | 3..60 | 928 | 256 | holds, 0 failures | fold_cells_N_3_60.log, 41 MB, 42 s |
| 1 | 61..62 | 62 | 512 | holds | fold_cells_N_61_62.log, 76 MB, 18 s |
| 2 | 63..80 | 648 | 512 | holds | fold_cells_N_63_80.log, 109 MB, 216 s |
| 3 | 81..90 | 430 | 512 | holds | fold_cells_N_81_90.log, 158 MB, 252 s |
| 4 | 91..94 | 186 | 1024 | holds | fold_cells_N_91_94.log, 293 MB, 232 s |
| 5 | 95..97 | 145 | 1024 | holds | fold_cells_N_95_97.log, 292 MB, 175 s |
| 6 | 98..100 | 149 | 1024 | holds | fold_cells_N_98_100.log, 299 MB, 302 s |
In all: **1 620 new cells for n = 61..100, 0 failures** (2 548 with the gate n ≤ 60). Each cell is the exact Smith form of an integer matrix mod 2^192 with every pivot below 2^152 (asserted), compared with the closed rule lowered by one, the free Z₂ counted at i = 0.

**Theorem C₇ (PROVED: pencil assembly + exact finite check).** **For every n ≤ 100, Syl₂ K(Q_n) ≅ (Z/2)^{a_n} ⊕ [Syl₂ K̄(n) with every exponent raised by one]**, and Syl₂ K̄(n) is the closed rule with every big clock lowered by one and the small layers shifted down (flight 6 §3.9). The cells n = 61..100 are new (the auditor stopped at 60; flight 6's certificates at 21, 23, 25, 27). *Dependencies:* §3.1 (Theorem RT/RT′, Lemma RT̄, Conjecture W = flights 1–4, flight 2's lattices), Lemmas H-odd/H-even (§2 A.5), the exact computation.
**Where the machine stops.** The cost is the Smith form of the largest half-size cell, ~D³: D = 512 took about 13 s, D = 1024 (first at λ = 94) took 70 s and 293 MB. D = 2048 first appears at λ = 126 (λ + 1 = 127 = 64 + 63, k = 6, I = {0, …, 5}, dim T(126) = 2¹², half 2048), i.e. at n = 126, and would need about 8 × 70 s ≈ 10 min for one cell — at the cap. So this engine can reach n ≤ 125 in principle (every family λ ≤ 125 has half-dimension ≤ 1024), at a cost of several hours of runs near the top.

### 4.2 What remains — the exact statement left open
- **For every n:** it suffices (§3.1) to prove, for every family, X̄(λ, i) ≅ 2X(λ, i). By Lemmas H-odd/H-even and P-R1 this is:
  - **odd λ = 2λ₁ + 1:** coker(2(2D + j) + (Ch − ε)Sh⁻¹) ≅ coker(F + 4(D + ⌈j/2⌉)) on N = T(λ₁), for every j — flight 6's (P) for the two series u·tanh(u/2) (j even) and u·coth(u/2) − 2 (j odd);
  - **even λ = ν + 1:** coker(1 + τ − a) ≅ coker(τ(τ + 2)/2) on T(ν), ν odd, for every i.
  Flight 6's conjugacies (Q), (Q_even) imply both; conjecture PL\* (§2 A.3) is the measured general form for odd families.
- **What a proof must use.** Not only the symmetric functions and the fold (PA.0), not only the divided powers of F and the floor (PB7.4): the Borel lattices that break the law are glued more deeply than tilting ones. Single Weyl and dual-Weyl lattices obey it (PN.1, PN.2: 96/96 each). So the natural next target is a statement about lattices with BOTH a Weyl and a dual-Weyl filtration (that is, tilting), e.g. an induction along the two moves in which each step keeps both filtrations of the folded half — «the mirror built piece by piece» with the pieces being Δ's and ∇'s.
- **For the machine:** the half-size engine reaches n ≤ 125 with D ≤ 1024 (about 70 s per D = 1024 cell, several hours of runs in all); n = 126 needs a D = 2048 cell, at the 10-minute cap.

## 5. Images — which served

- **The mirror built piece by piece (this flight's image) — SERVED as the question, not as a proof.** It told me to look for the reflection move by move (Route 1), and the dance does carry the folded operator one move at a time with a unit pivot at every level (A2.4, A.5). It also told me where the pieces come from: the measurements say the reflection can be rebuilt from pieces that are *functions of the floor*, as long as they agree with the constant pieces modulo 2 (PL\*); pieces that depend on the individual box inside a floor break it. What it did not give: the last piece, the 2^|I| × 2^|I| final matrix, where equal determinants are not enough.
- **The mirror that doubles — SERVED twice.** (1) Lemma A0: on one family, doubling is quotienting by e₂ (X[2] = e₂X), so the law is T/(τ, e₂) ≅ T/(τ, a − 1), two quotients by two different «mirrors». (2) A2.1–A2.2: in every family the folded and the doubled problems are the same diagonal operator on two lattices that differ only by odd units — the double factorials (2s − 1)!! for odd families, h = 2⌊c/2⌋ + 1 for even ones.
- **«Se van turnando» — SERVED as a control.** Without the sign (−1)^(D+i) of the turn the law fails in 53 of 60 calibration cells (Leg 0), and on T(0) = Z, where nothing alternates freely, it fails always.
- **«Binario, o está o no está… en el doble de horas» — SERVED lightly.** The unit h = 2⌊c/2⌋ + 1 is the clock rounded to the odd hour; it is exactly one factor 2 short of being a symmetric function (its finite differences are ±2^(r−1)).
- **The wound — SERVED in Leg C.** Computing on the coinvariants (Lemma H) heals the sink directly: the free summand at i = 0 is just the one zero eigenvalue on the top floor, so no limit over large shifts (Lemma Z0) is needed in a finite range.

## 6. Sealed predictions, hits and failures

All in checks/SEALED.md, each sealed (time pasted from `date`) before its run.
| id | prediction (odds) | ended |
|---|---|---|
| P0.1 | X = rule cell, λ ≤ 12, i ≤ 4 (99 %) | **held** 60/60 |
| P0.2 | X̄ = X lowered by one, same cells (98 %) | **held** 60/60 |
| P0.3 | controls: unlowered ≤ 2 (97 %), lowered by two ≤ 10 (90 %), sign-free fails ≥ 1 (90 %), λ = 0 fails (99 %) | **held** (1, 2, 53 fail, fails at i = 1..4) |
| **PA.0** | **the law holds on every Z₂[a]-free 𝓢-lattice (45 %)** | **FAILED**: 3/813 |
| PA.0c | non-free 𝓢-lattices fail ≥ 1 (95 %) | held (1964 fail) |
| PL.a | constant ζ keeps the cokernel, α = 2..4 (97 %) | held 825/825 |
| PL.b | floor-dependent ζ ≡ const mod 2 (40 %) | **held** 825/825 |
| PL.c | floor-dependent odd units on F and payment (30 %) | **held** 825/825 |
| PL.d | entry-wise ζ fails ≥ 1 (95 %) | held (197 fail) |
| **PL.f** | **arbitrary floor-dependent ζ keeps the cokernel (35 %)** | **FAILED**: 308/825 |
| PL.g | b and c together, l ≤ 16 (60 %) | **held** 1125/1125 |
| PL.h | α = 1 fails ≥ 1 (90 %) | held (150 fail) |
| **PL.i** | **the mod-2 condition relaxes at α = 6, 8 (50 %)** | **FAILED**: 104/275 at every α |
| PL.j | entry-wise ≡ const mod 2 fails at α = 8 (55 %) | held (26 fail) |
| PB7.1 | the law on Borel lattices (40 %; ≥ 150 kept) | first run had only 40 kept: 160/160, undecided |
| **PB7.2** | **(P) on all generated Borel lattices (40 %)** | **FAILED**: 154/2400 (non-kept included) |
| PB7.1′, PB7.3 | the law and (P) on kept Borel lattices, shallow generator (45 %, 35 %) | held 896/896, 896/896 |
| **PB7.4, PB7.5** | **the same with a harsher generator (70 %, 65 %)** | **FAILED**: 24/632 and 9/632 — Conjecture B refuted |
| PBG1, PBG1c | half-size = direct, λ ≤ 20, i ≤ 6 (98 %); control fails ≥ 1 (95 %) | held 140/140; control 128 |
| PBG2 | the law for n = 3..60 with my engine (99 %) | held, 928 cells |
| PC7.1 | the law for n = 61..93 (97 %) | held, and on to n = 100 (1 620 cells) |
| PN.1, PN.2 | the law on Δ(μ) (99 %) and on ∇(μ) (50 %), μ odd ≤ 31, i ≤ 6 | held 96/96 and 96/96 |
| **PC7.2** | **a 512-cell takes 20–120 s (60 %)** | **FAILED**: ~13 s |
**Failures, in the same type: PA.0, PL.f, PL.i, PB7.2, PB7.4, PB7.5, PC7.2.** The two that matter are PA.0 and PB7.4: the law is not a consequence of the symmetric functions, nor of the Borel structure.

## 7. My errors

- **E1 (typed times in CLAUDE.md).** The STATE lines written at 12:55 and at 13:35 carried times I typed («12:55», «13:40»; the second was in the future). Corrected at 13:35:40 with the pasted date. Every other time in this report and the diary is pasted.
- **E2 (a failed write reported as done).** At 13:35:10 a python heredoc that should have appended §2 A.4 to this report failed on an encoding error, but the same shell line also wrote a diary entry saying A.4 was written. I noticed at once (the grep showed no A.4), inserted A.4 by hand and wrote a correction line in the diary. From now on the diary line comes after the check, not in the same command. (A first hand-inserted heading also carried a typed time; replaced by the pasted bracket.)

- **E3 (a number written before it was computed).** In the first draft of §0 I wrote «2 254 new cells» for n = 61..95 without adding the run counts; the sum is 1 374 (62 + 648 + 430 + 186 + 48). Replaced at once, before any other step, and the diary says so.

- **E4 (a sketch first marked PROVED).** In §2 A2.4 I wrote «PROVED» for a second proof of the Steinberg case through the dance and determinants. Later in the same leg, while checking whether the class of perturbations is closed under «doblar» (A.3), I found that the divisibility by 2 at each level needs the even-index coefficients constant mod 2, which my propagation count only guarantees for about four levels. Downgraded to SKETCH (Sun Oct  4 14:07:30 CEST 2026) in A2.4, A.6 and §8; nothing else depended on it (Leg C uses Lemmas H-odd/H-even and exact computation, not A2.4).

## 8. The story of this flight, in plain words

- **A window that started twice.** I re-entered at 12:53 with the skeleton, the Leg 0 estimate and three notes already on disk from a first window (12:36–12:42). The first thing after re-reading was to finish the calibration: my own Smith form reproduced the cell law in 60 of 60 cells, and two controls taught something real — without the sign of the turn the law dies, and on T(0) it is simply false, because there the fold is a scalar.
- **First idea: maybe it is just algebra.** One family at a time, doubling is quotienting by e₂ (the note's §1.1 works inside every family, because a tilting module mod 2 is free over F₂[F]/F²). So the law is «T/(τ, e₂) ≅ T/(τ, a − 1)», and in the eigen-frame both ideals are the same on every eigenline. I hoped this was a general fact about lattices with the symmetric functions acting. I sealed it at 45 % and tested random such lattices: 810 held, 3 failed. Not algebra alone.
- **Second idea: write each family as one operator and two lattices.** For odd families the folded lattice is cosh(u/2)·N and the doubled one exp(F/4)·N — the same series up to the odd double factorials. For even families it is T against h·T with h = 2⌊c/2⌋ + 1. Everything became «one diagonal operator, two lattices that differ by odd units».
- **Third: which perturbations are harmless?** Flight 6 had seen that the higher divided powers of F never change the cokernel when their coefficients are constant, and do when they vary. I sorted the variations: coefficients that are functions of the floor, constant mod 2, are harmless (825/825, then 1125/1125 with odd units added), while anything that depends on the box inside a floor, or is not constant mod 2, breaks. That is a clean conjecture (PL\*), and a first-order count explains half of it.
- **Fourth: the Borel temptation, and its fall.** Then I asked whether the E's matter at all: random lattices with only the divided powers of F and the floor. With a gentle generator the law held 1056 times out of 1056 and I wrote, too quickly, that the law «lives in the Borel». I sealed a harsher test at 70 % and it failed in 24 cells. I struck the sentence. The law needs the whole tilting structure. That was the most useful failure of the flight: it tells the next pilot what any proof must use.
- **No proof, so the range.** Route 1 carried the fold through the dance one move at a time, with a unit pivot at every level; for Steinberg families I first thought this closed them again by determinants, and later saw that the per-level divisibility by 2 is not controlled (A2.4, downgraded, E4); in general it stops at the first «paso», where the final matrix is 2^|I| × 2^|I|. I closed Leg A as NO CONCLUYO. Then I re-derived flight 6's Ψ on the coinvariants (so it holds at shift 0 too) and the even-family form, which halves every matrix. With that, the auditor's n ≤ 60 took 42 seconds, and the fold law went to every n ≤ 100 (1 620 new cells, §4.1), all with exact integers. A last small test showed that single Weyl and dual-Weyl lattices obey the law: what breaks it in the Borel world is deep gluing, which tilting lattices control and random ones do not. That is where I would start the next flight.

## 9. Files with md5

(Sun Oct  4 14:07:00 CEST 2026, pasted. REPORT.md and logs/DIARY.md are still being written and are not listed; the list is also in logs/_md5_f7.txt; logs/md5_check.log was empty when hashed, its content is quoted below.)
**material/, vigia.sh and MISSION.md against MANIFEST_md5.txt (engines/md5_check.py, logs/md5_check.log, VIGIA-FIN-OK):** 283 match, 1 differs: **MISSION.md** (manifest 875a3084…, file timestamp Oct 4 12:52:02, i.e. before this window re-entered at 12:53). This window only read MISSION.md; the first window's diary (12:36–12:42) records no edit to it. I cannot tell who changed it; I report it as found.
```
c4f42394bf502b14055c948039c83929 CLAUDE.md
4a30a00e0f600208f3c0d38f011e8c93 checks/SEALED.md
19d1929ccee20de05c0f78b28dda165f engines/borel_lat.py
6e9dcfc48dc0114dc500157b98698fae engines/cal0.py
e9578f9eb0e08c91788e5a85e42b6c89 engines/fold_cells.py
03a2d07b83997dfcb4f6c974e3f642ea engines/gh_audit_vuelo2.py
e8ce426cbda1a7d612a30a664d68255e engines/gh_audit_vuelo6.py
4f4525596a5627713c996f2ebfd87206 engines/m7lib.py
bfa4f7f19c23c3f701024f599ec8737e engines/md5_check.py
46f39ea63b00df084c8f5462143e68e4 engines/nabla_test.py
5f0aa7481e7a93a22d4a916f38f57cc2 engines/pl_test.py
b978fc02e8293c3621fbffbabeaf2aa5 engines/s_lat.py
e3d9f8ea9a187a1d74144a07d39366de engines/tilt_dp.py
6e0d2683124ed5139c8471436bc6ae35 logs/borel_lat_400_deep.log
748435ff155f440aedb116f69fc2b21a logs/borel_lat_500_odd.log
735d2d8eaf18423f5f133bd47d14b4b6 logs/borel_lat_600.log
4a2a79c7c9d67e8073002f76bfc7f8b1 logs/cal0.log
3254fc3f46048b2041910080d4e139a7 logs/fold_cells_N_3_60.log
432bf88e05c2499cccc5c994ffe3b59d logs/fold_cells_N_61_62.log
d3a2c4179616ecb11c6e8faee88849b5 logs/fold_cells_N_63_80.log
7b52ef7f2aaf529ae661563fc0b75bc1 logs/fold_cells_N_81_90.log
d61ab4b924f32373b9ff31bdf6aa5cc3 logs/fold_cells_N_91_94.log
ac5c38b8f5de7764f5e45a82fc84eb6c logs/fold_cells_N_95_97.log
ad0a5c0b5f7396d4a0623db8b09cff35 logs/fold_cells_N_98_100.log
9e8b2c8892c0ee12f3abb0e0d86d5339 logs/fold_cells_V_20_6.log
d41d8cd98f00b204e9800998ecf8427e logs/md5_check.log
d9d5f406f7db9b3b217501268ffe9da0 logs/nabla_test_31_6.log
28022c1f2c6dfeabdf121618b538fec7 logs/pl_a.log
e32289822b38f472d750ba77f85360a5 logs/pl_a_alpha1.log
dbcad42e030cd12a522562a999fbcb57 logs/pl_b.log
96cf22db446c3beb045167ed37201084 logs/pl_c.log
d8e2f3edb6e7ec99785c61f0d7c557b7 logs/pl_d.log
d9e0588b0be10aef3f488c475f40ae5f logs/pl_e.log
e6087400981ec4f1658edd2ba2a529d9 logs/pl_e_a8.log
1b52fb44b49c03980a827862ab02f829 logs/pl_f.log
986e0579b3bbe288290aca6d8fb215bc logs/pl_f_a3.log
f31be958b61a259925a22eca0cb03582 logs/pl_f_a4.log
31e726d7da572618f5278793a86e08cb logs/pl_f_a6.log
dd94b60c6b1ac34c25d755de3387915e logs/pl_f_a8.log
3e075fa2249c2de5605869da4d9ebf35 logs/pl_g16.log
c1f4eb835c342ff20147e7ad72eb919d logs/s_lat_3000_5_3.log
94f9fae73389f3cb3492c98096f3a825 logs/s_lat_400_5_3.log
```
Notes.
- engines/tilt_dp.py and engines/gh_audit_vuelo2.py are copied unchanged from material/ (same md5 as the originals); engines/gh_audit_vuelo6.py is the auditor's file with its two paths changed from engines_gh/ to engines/ (Leg 0, diary 12:53).
- Engines edited after a first run, each declared in the diary before the next run: s_lat.py (balanced multiplicities, before logs/s_lat_3000_5_3.log), pl_test.py (variants f, g), borel_lat.py (option odd; option deep). The results of the earlier runs stand as logged; no run was repeated under the same sealed prediction except where SEALED.md says so (PA.0, PB7.1).
- fold_cells.py was not edited after its first run; every Leg B/C result comes from the same file (md5 above).
- CLAUDE.md was edited after the hash above, only in its STATE line (14:07:48, «FLIGHT WRITTEN»), as the mission orders; its final md5 is therefore not the one listed.
