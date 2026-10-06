# REPORT_COLD — cold reading of «The Dancing Sand Theorem»
Reader: «Grepy el lector frío del cubo 1». Started 2026-10-04.

## 0. First line — does the Dancing Sand Theorem hold as stated: HOLDS / HOLDS WITH GAPS / DOES NOT HOLD

**HOLDS.** Every link L1–L9 HOLDS on my cold reading (re-derived in my own words, §2), and every check I wrote with my own code agrees: the direct Laplacian Smith form for n = 2..13 (12/12, controls fire), Bai's table and counts, Gao et al.'s Thm 4.1–4.2, and a machine check of the heart (Theorem F's construction on every house λ ≤ 255, α ≤ 4, three prices: 0 failures; brute-force floor 1898/1898). **Three PRESENTATION remarks, none affecting the truth:** (1) the one-line statement in MISSION §1 omits the additive constant k + 2^k + κ(i−1, 2^k) of the big clocks and the convention at i = 0 (the flights' own D.5 has them right); (2) «integer antitonic fit» needs a property (adjacent PAVA blocks separated by an integer) that the proof uses and the text justifies only in part — it is true in every cell, by the same induction; (3) the multiplicities m_λ(n) are known (Larsen 2024 prints the same fusion rule; Donkin's characters give them), and two basis choices are standard (CSX, Gao et al.) — credit to add. As far as eleven web searches and the sources given can tell, this is the first statement and proof of the whole 2-part of K(Q_n); independent human verification and publication remain the real test.

## 1. The statement as I read it

**Claim (Dancing Sand Theorem).** For every n ≥ 1,
  `Syl_2 K(Q_n) ⊕ Z_2 ≅ ⊕_λ X(λ, (n−λ)/2)^{m_λ(n)}`,
the sum over λ ≡ n (mod 2), 1 ≤ λ ≤ n (λ = 0 never occurs for n ≥ 1), with:

- **Multiplicities** m_λ(n): start from V = T(1) at n = 1 and apply `V⊗T(0) = T(1)`, `V⊗T(2l+1) = T(2l+2)`, `V⊗T(2l+2) = T(2l+1)² ⊕ Φ(V⊗T(l))`, `Φ(T(ν)) = T(2ν+1)`. (Equivalently: peel Donkin's characters `ch T(λ) = ∏_{t<k}(e^{2^t}+e^{−2^t})·∏_{t∈I}(e^{2^t}+e^{−2^t})` off `(e+e^{−1})^n`.)
- **Data of a family:** `λ + 1 = 2^k + Σ_{t∈I} 2^t`, I ⊆ {0,…,k−1}, K = 2^k. «Dancers» D ⊆ I, `o_D = Σ_{t∈D} 2^t`; D ↔ the Weyl factor Δ(μ_D) of T(λ), `μ_D = λ − 2o_D`; o-order = o_D increasing (= μ decreasing). `next(t) = min{u ∈ I ∪ {k} : u > t}`, `h_t = next(t) − t`. κ(a, b) = number of carries in a + b = s_2(a) + s_2(b) − s_2(a+b).
- **X(λ, i) = ⊕_{a=1}^{k−1} (Z/2^a)^{2^{|I|+k−1−a}} ⊕ ⊕_{D⊆I} Z/2^{e_D}** («small clocks» and 2^{|I|} «big clocks»), where:
  - for **i ≥ 1**, m = i − 1: `R_μ(D) = Σ_{t∈D}(h_t − 2^t) − κ(μ, o_D)`, `x_D = R_m(D) − R_{m+K}(I∖D)`, ŷ = the integer antitonic fit of x in o-order (pool adjacent violators into a non-increasing sequence; a pool of p values with sum S becomes (S mod p) values ⌈S/p⌉ followed by ⌊S/p⌋), and **e_D = k + K + κ(m, K) + ŷ_D**;
  - for **i = 0**: e_∅ = ∞ (the Z_2), and the other 2^{|I|} − 1 clocks are flight 1's naive clocks `u(D) = B(μ_D, o_D) + Σ_{t∈D} h_t`, `B(μ, j) = Σ_{r=0}^{μ}(1 + v_2(j+r)) − v_2(μ!)`, pooled the same way (FLIGHT4 11.2.6(b) gives the equivalent «house m_low = 2^k − 1 with the row ∅ deleted»).
- For i ≥ 1 the two forms agree: `u(D) = B(μ_D, i + o_D) + Σ_{t∈D} h_t = k + K + κ(m, K) + x_D` value by value (my gate C-R0, 2520/2520 cells λ ≤ 63, i ≤ 40; on paper it is the carry identity κ(m, z) + κ(m+z, K) = κ(m, K) + κ(m+K, z) applied to flight 3's A.1).

**What is claimed to be proved** (FLIGHT4 §11.4): Theorem D (flight 2 + RT′ of flight 3) reduces X(λ, i) to the small clocks plus `2^k · coker M(λ, i)`, M an explicit 2^{|I|} × 2^{|I|} lower-triangular integer matrix; Theorem O gives `d_r(M) ≤ Y(r)` (Y = partial sums of the r smallest pooled clocks, shifted), the tropical bound gives `d_r(M) ≥ T(r)` (T = min cost of an r-matching in the support of M), and Theorem F gives `T(r) ≥ Y(r)`; hence `d_r = Y(r)` for every r: the Smith form of M is the pooled rule.

**PRESENTATION remarks on the statement as printed in MISSION.md §1** (the mathematics is unaffected):
- (S1) The display writes `Smith₂ M(λ, (n−λ)/2)` with exponents «the pooled clocks» PAVA(x_D). Read literally this is off by a constant: Theorem D has `2^k · coker M`, and the exponents of 2^k·coker M are **k + K + κ(m, K) + ŷ_D**, not ŷ_D (ŷ_D can be negative: e.g. λ = 6, i = 1 has x = (1, 1, −1, −1) by hand, constant 6, big clocks 7, 7, 5, 5, and X(6, 1) = {1:4, 5:2, 7:2}, which is also the auditor's printed cell in THE_FIRST_OPEN_CELL_M6). The constant is printed nowhere in one piece: flight 3 A.1 writes the clocks as `k + 1 + x_D` with a different x_D, and flight 4 A.4 drops «global constants». A reader must rebuild it (I did, and gated it).
- (S2) The formula for x_D needs m = i − 1 ≥ 0; the cell i = 0 (one free Z per family with λ = n) needs its own convention, which the display does not give.
- (S3) «PAVA» alone is the real isotonic regression; the integer splitting convention is part of the statement and should be printed (it acts: pools with non-integer means occur).

## 2. The chain, link by link (L1–L9: statement, verdict, doubts, external facts)

### L1 — the tilting families and their multiplicities (fusion recursion). Verdict: **HOLDS**
*Statement (my words).* Over Z_2, V^{⊗n} is a direct sum of explicit lattices T_dance(λ) (built from Z by «doblar» Φ, `T(2l+1) = Φ(T(l))`, and «dar un paso» V⊗, `T(2l+2) = V⊗Φ(T(l))`), with multiplicities m_λ(n) given by the fusion recursion of §1.
*Re-derived.* The recursion is forced by three isomorphisms: `V⊗T(0) = V = Φ(Z)` (Φ(Z) has F(b0) = b1, E(b1) = b0·(Ω − H²)·1 = b0 since Ω = 1, H = 0 on Z); `V⊗T(2l+1) = T(2l+2)` (definition); `V⊗V⊗Φ(N) ≅ Φ(N)² ⊕ Φ(V⊗N)` (the content of L2/RT′, re-derived there). Characters are consistent: `(e+e^{−1})²·(e+e^{−1})·χ(e²) = 2(e+e^{−1})χ(e²) + (e+e^{−1})(e²+e^{−2})χ(e²)`.
*Doubts.* None on the mathematics. The identification of T_dance(λ) ⊗ F_2 with the indecomposable tilting module T(λ) (Donkin) is **not used** by the proof (RT′ works with T_dance directly); it only justifies the name «tilting families». The sentence of MISSION §1 «the tilting families λ of V^{⊗n} for SL₂ in characteristic 2» is therefore interpretation, not a dependency.
*External facts.* Donkin's tensor product theorem at p = 2 — used only for the cross-check by characters (my C-M0: fusion = peeling for n ≤ 64, 64/64) and for the name. Correctly used.
*Machine.* C-M0 held 64/64, with Σ m_λ dim T(λ) = 2^n.

### L2 — Theorem RT / RT′: the sandpile group splits family by family. Verdict: **HOLDS**
*Statement.* `Syl_2 K(Q_n) ⊕ Z_2 = coker(σ on V^{⊗n} ⊗ Z_2) ≅ ⊕_λ X(λ, (n−λ)/2)^{m_λ(n)}`, `X(λ, i) = coker(F + λ − H + 2i on T_dance(λ))`.
*Re-derived, step by step.*
1. *Dictionary.* With s_i = 1 − x_i and s_S = ∏_{i∈S} s_i (a unitriangular Z-basis of Z[(Z/2)^n]), the Laplacian element L = Σ_i(1 − x_i) acts by `s_i s_S = s_{S∪i}` (i ∉ S) and `s_i s_S = 2 s_S` (i ∈ S, since s_i² = 2s_i): so multiplication by L is σ = U + 2D, and coker σ = coker(Laplacian matrix) = K(Q_n) ⊕ Z. Under s_S ↦ (b1 on S, b0 elsewhere), U = F (F primitive), D = (n − H)/2: σ = F + n − H, an element of Dist_Z(SL_2). Any isomorphism of Dist-lattices carries σ; on a summand of top weight λ, σ = F + (λ − H) + 2(n−λ)/2. ✓
2. *Lemma W* (FLIGHT3 0.2): if N has weights in [−λ, λ], every lattice extension of Δ_A(λ) by N splits. I re-did it: lift v to x of weight λ; E^{(s)}x = 0 (weight λ+2s absent), F^{(r)}x = 0 for r > λ (weight < −λ absent); by Kostant's formula E^{(s)}F^{(r)}x = C(λ−r+s, s)F^{(r−s)}x, the same constants as on v; so e_r ↦ F^{(r)}x is a Dist-map splitting the extension. ✓
3. *Ext¹(Δ_A(λ), ∇_A(μ)) = 0* by Lemma W for μ ≤ λ and by the duality τ (exact on lattices) for μ > λ; Hom(Δ(λ), ∇(μ)) = δ A. Induction on filtrations gives Ext¹_A(M, N) = 0 for Δ-filtered M, ∇-filtered N, hence `Hom_A(M, N) → Hom_k(M_k, N_k)` onto (long exact sequence of 0 → N →·2 N → N_k → 0; any extension of lattices is a lattice, so Ext in lattices is enough). ✓
4. *Filtrations.* Δ_A(m)⊗V ⊃ the span of `F^{(r)}(v⊗b0) = F^{(r)}v⊗b0 + F^{(r−1)}v⊗b1` (r = 0..m+1), saturated, ≅ Δ_A(m+1) by the universal property; the quotient is generated by the image v′ of v⊗b1 (E v′ = image of v⊗b0 = 0, E^{(s≥2)}(v⊗b1) = 0), with basis F^{(s)}v′, s < m (F^{(m)}v⊗b1 = F^{(m+1)}(v⊗b0) lies in the sub), so ≅ Δ_A(m−1). ∇ by duality (V self-dual). Φ(Δ(μ)) ≅ Δ(2μ+1): the F-chain of Φ(Δ(μ)) has coefficients 1, 2(r+1), against 2r+1, 2r+2 for Δ(2μ+1); the diagonal rescaling c_{2r+1} = (2r+1)c_{2r}, c_{2r+2} = c_{2r+1} uses odd numbers only, and E is forced by [E, F] = H on an irreducible F-chain over Q. ✓ (Φ is a Dist_{Z_2}-lattice: FLIGHT2 A.1(a)(b), checked by me for F^{(2s)}, F^{(2s+1)} on both slots; the E-side read, not redone in full.)
5. *The identity mod 2.* Over F_2: Δ(3) ⊂ V^{⊗3} has form values C(3, r) = 1, 3, 3, 1 (units), so V^{⊗3} = Δ(3) ⊕ Δ(3)^⊥; on the weight-1 part of the ⊥, E = 0 so EF = H = 1 and each {p, Fp} spans a copy of V: ⊥ ≅ V². Δ(3) ≅ V⊗V^{[1]} (image of b0⊗w0 contains b0w0, b1w0, b0w1 = F^{(2)}(b0w0), b1w1). With Φ(N)_k ≅ V⊗N_k^{[1]} and (V⊗N)^{[1]} = V^{[1]}⊗N^{[1]}: `(V⊗V⊗Φ(N))_k ≅ Φ(V⊗N)_k ⊕ Φ(N)_k²`. ✓
6. *Lifting.* Both sides have Δ_A- and ∇_A-filtrations (4), so the mod-2 isomorphism and its inverse lift (3); gf ≡ 1 mod 2 means gf = 1 + 2h with h a Dist-endomorphism (torsion-free), invertible over the complete ring Z_2. ✓
*Doubts (where they live).* (i) FLIGHT1's RT cited Jantzen II.4/II.E; FLIGHT3 0.2 found II.4 is over a field (an ERROR of citation in FLIGHT2 Leg 0 item 3) and replaced the whole citation chain by steps 2–6. I agree with that replacement; RT′ is the version the theorem should cite. (ii) Kostant's commutation formula in Dist_Z(SL_2) is the one external fact; it is standard (Kostant's Z-form; e.g. Humphreys, *Introduction to Lie algebras*, §26) and correctly used. (iii) The step «Hom_A(Δ(λ), ∇(λ)) ≠ 0 exists by Lemma W's construction» is stated a little quickly in FLIGHT3, but it is not needed for steps 3–6 (only Ext¹ = 0 is used).
*Machine.* Check 1 (§3.1): the whole chain RT′ + D + O + F, against the direct Laplacian, n = 2..13, 12/12.

### L3 — Bier's basis (Theorem Z), the two moves «doblar» Φ and «dar un paso» V⊗Φ, P-R1. Verdict: **HOLDS** (Theorem Z: HOLDS but **not a dependency** of the theorem)
*Statement.* (a) Theorem Z: Bier's vectors η_{j,k}(J) = F^{(k−j)}e_J (J ballot, j ≤ min(k, n−k)) are a Z-basis of every floor. (b) P-R1: for any graded lattice N (F lowering the floor by one) and α ≥ 1, `coker σ^{(α)}_j on Φ(N) = (rank N units) ⊕ 2·coker σ^{(2α)}_{⌈j/2⌉} on N`. (c) The even step: on V⊗Φ(N), `coker σ = (2 rank N units) ⊕ 2·coker [[F + π_A, 0], [κ, F + π_C]]` on N ⊕ N, `π_A(f) = −π(2f)π(2f+1)/2`, `π_C(f) = −π(2f+1)π(2f+2)/2`, `κ(f) = −π(2f+1)`.
*Re-derived.* (b) σ(b0 n) = b1 n + 2^α(j+2f) b0 n eliminates every b1 n with a unit pivot; σ(b1 n) becomes `2F n − 2^{2α}(j+2f)(j+2f+1) n`, and `(j+2f)(j+2f+1)/2 = (⌈j/2⌉+f)·u_f`, u_f odd (j+2f+1 if j even, j+2f if j odd); right-multiplying by U^{−1} and conjugating by floor scalars s_{f+1} = −s_f/u_f gives `−2(F + 2^{2α}(⌈j/2⌉ + D))`. (c) From the coproduct: F(A) = B + 2C, F(B) = 2A·F, F(C) = Dd, F(Dd) = 2C·F (A = b0⊗b0, B = b0⊗b1 − b1⊗b0, C = b1⊗b0, Dd = b1⊗b1; floors 2f, 2f+1, 2f+1, 2f+2); eliminating B and Dd (coefficient 1) leaves exactly the 2×2 block system. **Both moves use only F and the floor grading, not E**: they are statements about a graded nilpotent operator and hold for any lattice. (a) Pascal induction with the ballot split B_j(n) = B_j(n−1) ⊔ (B_{j−1}(n−1)+{n}) re-read; block-triangular with unimodular diagonal blocks in both cases k ≤ n/2 and k > n/2. 
*Doubts.* None in (b), (c). Theorem Z, Theorem B and Theorem L (the kiss matrix) are used **only** for side results of flight 1 (stable floors, landing); the final chain RT′ → D → O → F never uses Bier's basis. The mission's table lists Theorem Z as part of L3; it should be listed as context, not as a link.
*External facts.* Bier 1993 (unimodularity of E_k for k ≤ n/2; cited through CSX Thm 3.1) — reproved by the Pascal induction, so the citation is decorative; correctly attributed.

### L4 — Theorem D: X(λ, i) = small clocks ⊕ 2^k·coker M(λ, i). Verdict: **HOLDS**
*Statement.* After the k dance steps that take T(λ) to 2^{|I|} copies of Z, `X(λ, i) = ⊕_{h=2}^{k}(Z/2^{h−1})^{2^{k+|I|−h}} ⊕ 2^k·coker M`, `M_{DD'} = −2^{1−2^k}·a_k(D∖D')·2^{o_D−o_{D'}}·∏_{d=o_D}^{o_{D'}+2^k−1} 2(i+d)` for D' ⊆ D (0 otherwise), a_k(Δ) = coefficient of y^Δ in q_k, `q_0 = −1`, `q_{t+1} = q_t² − [t ∈ I] y_t q_t` in Z[y_t]/(y_t²).
*Re-derived.* (1) **The coupled recursion (FLIGHT2 C.0).** For a lower-triangular system G = diag(F + π_s) + Σ K_{ss'} on N^{⊕r} with N = Φ(N′): eliminating b1 n_{s′} by G(b0 n_{s′}) and substituting into G(b1 n_{s′}) gives exactly `π'_s = −π_s(2f)π_s(2f+1)/2` and `K'_{ss'} = −[π_{s'}(2f+1)K_{ss'}(2f) + K_{ss'}(2f+1)π_s(2f) + Σ_{s''} K_{s''s'}(2f+1)K_{ss''}(2f)]/2`; for N = V⊗Φ(N′) the same elimination slot by slot gives the A, C dancers with `K_{(s',A)→(s,C)} = −K_{ss'}(2f+1)`, `K_{(s',A)→(s',C)} = −π_{s'}(2f+1)` and no C→A term. I did both eliminations by hand. Divisions by 2 are exact because all entries keep valuation ≥ 1 (products of two such, halved). Each level makes exactly half the rank unit pivots and multiplies the rest by 2: the small clocks come out as stated (count: 2^{k+|I|−h} units at level h, raised h−1 times). (2) **Windows.** By induction every π_s^{(h)}(f) is a constant times ∏ π over [2^h f + o_s, 2^h f + o_s + 2^h − 1] and every K_{ss'}^{(h)}(f) over [2^h f + o_s, 2^h f + o_{s'} + 2^h − 1]: the three kinds of terms in K' are products over two adjacent intervals with the same union. (3) **Coefficients.** c(x) = Σ c_Δ x^Δ obeys c ← −c²/2 (doblar) and c ← −c²/2 − x_t c (split): the intermediate dancer s'' ↔ ordered splittings Δ = Δ1 ⊔ Δ2. With c = −2^{1−2^h}q and y_t = 2^{2^t}x_t: q ← q² − y_t q, q_0 = −1 (checked both moves). (4) y^Δ = 2^{o(Δ)}x^Δ gives the factor 2^{o_D − o_{D'}}.
*Doubts.* None. One remark: the closed form is stated for α = 1 (payments 2(i+d)); the flights use σ^{(α)} with 2^α(i+d) throughout and the same proof works.
*External facts.* None.

### L5 — the cost form: valuations of M = rulers (carries) + gold γ. Verdict: **HOLDS**
*Statement.* For D' ⊆ D (a = D, b = D'), i ≥ 1, m = i − 1: `v_2(M_{ab}) = αK + κ(m, K) + R_m(a) − R_{m+K}(b) + γ(a∖b)`, with `γ(Δ) = Σ_{u∈I∖Δ, u > min Δ} h_u` (the gaps skipped by Δ), and the deficit law `v_2(a_k(Δ)) = k − |Δ| − min Δ =: δ(Δ)`.
*Re-derived.* (1) **Deficit law** (FLIGHT2 C.4(iv)): at t = max Δ + 1, a_{t}(Δ) = −a_{t−1}(Δ∖max Δ) (q_{t−1}² has no y_{maxΔ}); above, `a_{t+1}(Δ) = 2a_t(Δ) + 2Σ_{unordered splittings} a_t(Δ1)a_t(Δ2)` and each cross term is ≥ t − max Δ ≥ 1 deeper than 2a_t(Δ) (one of min Δ1, min Δ2 is min Δ, the other ≤ max Δ). ✓ (2) v(M_{ab}) = 1 − 2^k + δ(Δ) + o(Δ) + Σ_{d=o_a}^{o_b+K−1}(α + v_2(i+d)) = 1 + δ(Δ) + Σ_d w(d), w = α − 1 + v_2(i+d). (3) Legendre: Σ_{d=x}^{y−1} v_2(i+d) = (y−x) − s_2(m+y) + s_2(m+x). (4) The identity **δ(Δ) = G(Δ) + γ(Δ)** (G = Σ_{t∈Δ}(h_t − 1)), because k − min Δ = Σ_{t∈I, t ≥ min Δ} h_t (telescoping). Putting (2)–(4) together, v(M_{ab}) − [R_m(a) − R_{m+K}(b) + γ(a∖b)] = 1 + αK + s_2(m) − s_2(m+K) = αK + κ(m, K), a constant of the cell. ✓ This is exactly the constant of my §1 (big clock = k + αK + κ(m, K) + ŷ_D).
*Doubts.* The i = 0 cell (π(0) = 0, the row ∅ vanishes) needs its own bookkeeping (FLIGHT3 A.3 «A(D) = α o_D − min D»); read, consistent with the B-form, not re-derived separately — covered by L9 and by check 1 (every n has its λ = n cell at i = 0).
*External facts.* Kummer's theorem (carries) and Legendre's formula — used correctly (in the elementary form κ(a,b) = s_2(a) + s_2(b) − s_2(a+b), v_2(n!) = n − s_2(n)).

### L6 — Theorem O: d_r ≤ Y(r) through the unique cheapest matching of the natural minor. Verdict: **HOLDS**
*Statement.* For every I and r, the assignment L_r → F_r (last r dancers to first r, σ(D) ⊆ D) of least Σ δ(D∖σ(D)) is unique, with value Σ_{D∈L_r} ε(D), ε(D) = G(D) − G(I∖D). Since v(M_{DD'}) = ρ_D + κ_{D'} + δ(D∖D') with potentials ρ, κ (constant over all perfect matchings L_r → F_r), the natural minor's determinant has a unique term of least valuation, so `v(det M[L_r, F_r]) = U(r)` (sum of the last r naive clocks, normalised) and `d_r ≤ U(r)`; then `d_r ≤ Y(r)` by convexity.
*Re-derived.* (1) Lemma B.3 (remove the top digit c, h = k − c): δ_I(Δ) = δ_{I'}(Δ∖c) + h[Δ ≠ ∅] − [c ∈ Δ]; strict subadditivity δ(Δ1) + δ(Δ2) − δ(Δ1⊔Δ2) = k − max(min Δ1, min Δ2) ≥ 1. (2) Induction: r ≤ N/2 is the (I', r) problem plus r(h − 1); for r = N/2 + s the T-columns are forced from T-rows, the matching becomes a degree-balanced descending multigraph on 2^{I'} (out − in = [L'_s] − [F'_s]), which splits into loops and descending paths; shortcutting a path of length ≥ 2 saves ≥ 1 per merge; equality forces paths of length 1, no non-loop T→T or B→B pair (each costs h ≥ 1 more), and then each node type (in L'_s ∩ F'_s, in neither, in L'_s∖F'_s, in F'_s∖L'_s) has exactly one possible edge set. Value: Σ_{L_r} ε_I = (N/2 − s)(h−1) + Σ_{L'_s} ε_{I'} (Σ over 2^{I'} of ε_{I'} is 0). ✓ (3) Lemma ε (the carries of 2^{t+1} run through the gap positions of [0,k)∖I) ✓. (4) **Convexity step, which the flights state in one word.** I proved it: d is convex with integer increments, d(0) = 0 and d ≤ U at the ends of every PAVA block (where Y = U); inside a block of p values with sum S = qp + ρ, Y rises by q (p − ρ times) then q + 1 (ρ times); if d(r*) > Y(r*) in the first part, some slope of d before r* is ≥ q + 1, hence all later ones, and d overshoots Y = U at the block's end; if in the second part, some slope after r* is ≤ q, hence all earlier ones, and d(r*) ≤ Y(r*). So **d ≤ Y**. ✓
*Doubts.* (i) The identification «natural minor value = U(r) = Σ_{L_r}(u(D) − k)» uses u(D) − k = ρ_D + κ_{I∖D} + ε(D) (FLIGHT2 C.5, «PROVED») and F_r = {I∖D : D ∈ L_r}; I did not redo the Kummer bookkeeping of C.5 by hand, but my gate C-R0 checks the equivalent statement (naive clocks = constant + x_D, value by value) on 2520 cells, and L5 gives the potentials. (ii) The convexity step deserves to be written in the paper (it is one paragraph; above).
*External facts.* None beyond the elementary fact that a unique least-valuation term determines the valuation of a sum.

### L7 — Theorems U and F: the floor T(r) ≥ Y(r) for every matching, family, α ≥ 1, shift. Verdict on pencil: **HOLDS, with one PRESENTATION gap (integer splitting)**; machine gate in §3.4
*Statement.* In every cell, every r-matching of the support of M costs at least the sum of the r smallest pooled clocks (normalised).
*How I read it, step by step (FLIGHT4 A.5, 11.2.1–11.2.6).*
1. **Theorem U / U° (one line).** If V is non-increasing in o-order, V(D) − V(I∖D) = ŷ_D, and V(a) − V(e) ≤ R(a) − R(e) + γ(a∖e) for e ⊊ a, then for any r-matching with rows A and columns B: cost ≥ Σ_A V − Σ_B V ≥ Σ_{L_r} V − Σ_{F_r} V = Σ_{L_r} ŷ = Y(r) (V non-increasing puts the r smallest values on L_r and the r largest on F_r = {I∖D : D ∈ L_r}; loops cost 0 = V(a) − V(a)). ✓ Re-derived.
2. **Windows as gates (11.2.1).** Inside W_t = [t, next(t)) the digit d = [t ∈ D] and the incoming carry c produce κ_t carries iff (type 1: d ∨ c) / (type 0: d ∧ c), and a carry leaves iff the window is saturated (κ_t = h_t). I redid the four cases bit by bit for both types (for type 1, (1,1) gives 1 + min(r_{t+1}, h−1) = min(r_t, h) carries). Hence R(D) = τ(D) − Σ_t κ_t c_t(D)[type 1 ∧ t ∉ D or type 0 ∧ t ∈ D], τ_t = h_t − α2^t − [type 1]κ_t. ✓
3. **Houses, penalties, top-digit recursion (11.2.2).** κ(m, o_D) = κ(m_low, o_D) + J(D)·r_k(m) (the carry out of bit k−1 continues through the ones of m above k), so every real cell is the base cell of its house with penalties (r_k(m), 0) or (0, r_k(m+K)) on the up-set J; removing the top digit c gives `R(D₀) = R′(D₀) − [T=1]κJ′(D₀)`, `R(D₀+c) = τ + R′(D₀) − [T=0]κJ′(D₀)`, `J(D₀) = [T=1]σJ′(D₀)`, `J(D₀+c) = [T=1]σ + [T=0]σJ′(D₀)`, γ_I = γ_{I′} + h on same-half arrows and = γ_{I′} on arrows that drop c. All re-derived. ✓
4. **The induction (11.2.6), each step checked:** (1) the walk: the first-half clocks are x′ + d₁ with d₁ integer, non-increasing, with steps only at the J′-boundary and its mirror; by Cut_{j−1} these are real block boundaries, so the real fit shifts by d₁ (KKT: constant shift on each block, monotonicity kept) and ŷ_j = [max(X1, 0), min(X2, 0)] (if the last X1 < 0 the merged central block is symmetric with sum 0; every prefix of it has sum ≤ 0, checked including prefixes that cross the junction). (2) Λ_j: −τ ≤ α2^c (type 1), −τ + κ ≤ α2^c (type 0). (3) Cut_j in the three saturated cases: the element next to the boundary has value ≥ α (case a, b) or ≤ −α (case c), so it is the floor/ceil value of a block of mean ≥ 1 or ≤ −1, which is not absorbed by the central block. (4) v′ = R_j + φ(·∖c) satisfies (G) with slack ≥ h on same-half arrows, and (E) with X1, X2. (5) Junction: v′({c}) − v′(I′) = −X1(I′) ≤ h − α. (7) The plumber's interval [max(c3, v′(p*)), min(c4, v′(p))] is non-empty because c3 − c4 = X1(f) ≤ 0 and v′(p) − v′(p*) = X1(p) > 0. (8) (G) for every arrow with one or both ends in the new flat: I checked the six cases; the two same-half cases use exactly «slack ≥ h» against «junction ≤ h − α», leaving α > 0. ✓
5. **From the base cell to real cells (L9) and i = 0:** see L9.
*Machine.* Check 4 (§3.4): my own implementation of the construction passes every check on every house λ ≤ 255, α ≤ 4, with three prices; the brute-force floor holds in 1898/1898 cells. **Final verdict: HOLDS** (with the presentation gap below).
*Doubts (where they live).*
- **(PRESENTATION gap — integer splitting.)** «Integer antitonic fit» splits each real PAVA block separately («ceil first»). For a general sequence this need not be antitonic: x = (1, 2, 0, 1, 2, 2) has real blocks of means 3/2 and 5/4 and integer split (2, 1, 2, 1, 1, 1). FLIGHT4's closing remark only excludes *equal* non-integer neighbouring means; what is needed (and true, by the same induction) is **⌊μ_A⌋ ≥ ⌈μ_B⌉ for every pair of adjacent blocks A, B**: integer shifts d_A ≥ d_B preserve it, the central block 0 has neighbours of mean > 0 (floor ≥ 0) and < 0 (ceil ≤ 0), and the junction without merge has μ ≥ 0, so ⌊μ⌋ ≥ ⌈−μ⌉. With this, the integer fit is antitonic, equals [max(X1,0), min(X2,0)], and Y(r) is the sum of the r smallest values. The group itself depends only on the multiset, so the theorem is unaffected; the proof's step 1 (shifting the integer fit) does need it, and the paper should state it.
- The level set F = {ŷ_j = 0} used in step 7 can be larger than the real central block (blocks of real mean in (0, 1) contribute their zeros); the proof works with values, not blocks, so this is harmless, but the text calls F «the central block» in (W) and «the central flat» in step 7: two different objects with one name.
- The proof was written in four minutes (20:08–20:12 by the diary) and gated afterwards; my reading found every inequality in place.
*External facts.* PAVA (Ayer–Brunk–Ewing–Reid–Silverman 1955): only the block characterisation (a fit is the antitonic regression iff it is antitonic and every block's prefix means are ≤ its mean) is used, correctly. LP duality / König are used only in superseded parts (A.1–A.6) and not in Theorem F.


### L8 — the tropical bound d_r ≥ T(r), PAVA and integer splitting: closes d_r = Y(r). Verdict: **HOLDS** (with the L7 presentation gap)
*Statement.* d_r(M) (least valuation of an r×r minor = sum of the r smallest Smith exponents) is ≥ the least cost of an r-matching in the support (each Leibniz term of a minor is a product along a matching); with d_r ≤ Y(r) (L6) and T(r) ≥ Y(r) (L7): d_r = Y(r) for every r, so the Smith exponents are the successive differences of Y, i.e. the pooled clocks.
*Re-derived.* The tropical bound is the ultrametric inequality. The step «d ≤ U at block ends and convex with integer increments ⟹ d ≤ Y» is my proof in L6 (4). The real isotonic regression = slopes of the greatest convex minorant of the cumulative sums (Ayer–Brunk–Ewing–Reid–Silverman 1955; Barlow–Bartholomew–Bremner–Brunk 1972): used correctly for the real fit; the integer version is the flights' own convention and needs the integer-separation property of L7's doubt (true in every cell: proved by the induction, gated P-INT).
*Doubts.* Only the presentation gap of L7 (the integer splitting must be shown antitonic; it is, in the cube's cells).
*Machine.* C4b: T(r) ≤ d_r = Y(r) ≤ … in 1898/1898 brute-force cells.

### L9 — from the base cell to every real cell, and the shift i = 0. Verdict: **HOLDS**
*Statement.* (a) For i ≥ 1 the real cell (λ, i) is the base cell of the house (I, k, m_low = (i−1) mod 2^k, α) with penalties (r_k(m), 0) or (0, r_k(m+K)) on the carry-out set J; since a jump never cuts a block (Cut_n), the pooled clocks of the cell are the base pooled clocks shifted by the penalty, and v = V − P_r J, w = V − P_c J certify Theorem U. (b) At i = 0 the row ∅ of M vanishes (the room payment 2(0 + 0)); the other rows are the base cell of the house m_low = 2^k − 1 with the row ∅ deleted (J = [D ≠ ∅]), Cut at position 1 gives PAVA(x)[1:] = PAVA(x[1:]), and V restricted certifies Theorem U because F_r (r ≤ N − 1) never contains the column I, mirror of the missing row.
*Re-derived.* (a) κ(m, o_D) = κ(m_low, o_D) + J(D)·r_k(m) (the carry out of bit k − 1 runs through the ones of m above k), and r_k(m+K) = 0 when r_k(m) ≥ 1, = v_2(⌊m/K⌋ + 2) otherwise. The penalty shift s(D) = −P_r J(D) + P_c J(I∖D) is non-increasing with steps only at the J-boundary and its mirror, so by Cut_n it is constant on blocks. (b) With Legendre at i = 0: Σ_{d=o_D}^{o_{D'}+K−1} v_2(d) = (K + o_{D'} − o_D) − s_2(o_{D'} + K − 1) + s_2(o_D − 1), which is the formula with «m = −1»; and κ(2^k − 1, o_D) = k + |D| − 1 − s_2(o_D − 1) for D ≠ ∅ turns it into R(D) − R(D′) + γ + constant for the house 2^k − 1. ✓
*Doubts.* None.
*Machine.* C4 (penalty form 686 169/686 169; Theorem U in every real cell checked) and C4-i0 (120/120 families λ ≤ 127: valuations, rule clocks and Theorem U at i = 0); check 1 contains an i = 0 cell for every n.

## 3. Checks with my own code (with controls)

### 3.0 Engine gate C-G0 — HELD (logs/gate0.log, VIGIA-FIN-OK, 23 MB, 2 s)
My engine `engines/mysmith.c` (my code: exact arithmetic in Z/2^64, pivots by increasing 2-adic valuation, row operations only; an entry ≡ 0 mod 2^64 at the end is reported as Z) against PARI/GP `matsnf` (an independent implementation over Z): 60/60 random integer matrices (sizes 4–40, mixed valuations, 15 singular, 15 all-even) and 7/7 Laplacians of Q_n, n = 1..7, give the same 2-adic exponents. Control: removing one factor from my answer is detected. (Sealed S1 C-G0, 95 %: hit.)

### 3.0b The rule, coded by me twice (logs/rule_gates.log, VIGIA-FIN-OK, 12 MB, 0 s)
`engines/myrule.py` (my code, from the printed statements only): (i) flight 1's form (naive staircase clocks B(μ, j) = Σ_{r=0}^{μ}(1 + v_2(j+r)) − v_2(μ!) plus transfers Σ(next(t) − t) over the minus signs, pooled by μ decreasing); (ii) the mission's form (x_D = R_m(D) − R_{m+K}(I∖D), pooled in o-order) plus the constant k + 2^k + κ(m, 2^k), which the mission's §1 does not print (see §1). **C-R0 HELD:** the naive clocks agree value by value in 2520/2520 cells (λ ≤ 63, 1 ≤ i ≤ 40), hence also after pooling; the control (constant without κ(m, 2^k)) differs in 760 cells. **C-M0 HELD:** the fusion recursion and peeling of Donkin's characters give the same m_λ(n) for n = 1..64. Pooling changes the clocks in 743 of the 2520 cells; in the cube it first enters at **n = 6, family λ = 4, i = 1**.

### 3.1 Check 1 — the direct computation (logs/check1_2_11.log, VIGIA-FIN-OK) — HELD
For n = 2..11 my engine computed the 2-adic Smith form of the full Laplacian L = nI − A of Q_n (2^n × 2^n, built in place; n = 11 in 0.1 s: the elimination stays sparse). In every case: **the rule as printed (both forms, my code) equals the direct group**, the number of non-trivial 2-factors is 2^{n−1} − 1 and exactly one diagonal entry is ≡ 0 mod 2^64 (the Z).
| n | Syl_2 K(Q_n) (exponent:multiplicity), direct = rule |
|---|---|
| 2 | {2:1} |
| 3 | {1:1, 3:2} |
| 4 | {1:2, 3:4, 5:1} |
| 5 | {1:6, 3:4, 4:1, 6:4} |
| 6 | {1:12, 2:4, 3:1, 5:4, 6:10} |
| 7 | {1:28, 2:1, 4:8, 5:6, 6:14, 7:6} |
| 8 | {1:56, 2:2, 4:16, 5:12, 6:28, 7:12, 10:1} |
| 9 | {1:120, 2:10, 4:16, 5:26, 6:48, 7:26, 9:1, 11:8} |
| 10 | {1:240, 2:36, 3:26, 5:16, 6:148, 8:1, 10:26, 11:18} |
| 11 | {1:496, 2:66, 3:32, 4:100, 6:164, 7:1, 9:100, 11:64} |
| 12 | {1:992, 2:132, 3:64, 4:200, 5:164, 6:1, 8:164, 9:201, 11:128, 13:1} (logs/check1_12_13.log, 1.3 s) |
| 13 | {1:2016, 2:364, 3:64, 4:364, 5:1, 7:560, 8:12, 9:364, 10:1, 11:336, 12:1, 14:12} (9.5 s, peak 533 MB) |
**Controls (each can fail, and does):**
- (a) **no pooling** differs at n = 6 ({5:8, 6:2, 7:4} instead of {5:4, 6:10}) and at n = 10; it agrees at n = 7, 8, 9, 11 (no pooled family cell occurs there with an effect).
- (b) **carries read at m instead of m + K** differs at n = 6, 10, 11, 12 and 13.
- (a) also fires at n = 12 (the 128 factors 2^11 become 44 × 2^10, 40 × 2^11, 44 × 2^12), not at n = 13.
So the cube up to n = 11 does see both ingredients, but **only weakly**: in 7 of the 10 cells the no-pooling control does not fire. The direct check alone cannot certify the pooling; that is why check 4 (small families, many shifts) matters.

### 3.2 Machine gates of L3–L6 (my code: engines/part2.py; logs/p2_L34.log, p2_L5.log, p2_L6.log; all VIGIA-FIN-OK)
- **G-L34 HELD, 1230/1230** (every λ ≤ 30, i = 0..40): the 2-adic Smith form of σ = F + 2(i + floor) on **my own explicit lattices T_dance(λ)** (built from Z by Φ and V⊗, F only; dim up to 256), computed by my C engine, equals the small clocks ⊕ 2^k·coker M with M from Theorem D's closed form (my exact rational 2-adic Smith), and equals the rule. Control: dropping the factor 2^{o_D − o_{D'}} changes Smith(M) in 191 of 240 cells. (This checks L3 and L4 as statements about σ; it does not check RT′, which only check 1 tests.)
- **G-L5 HELD, 87 360/87 360** entries (λ ≤ 63, 1 ≤ i ≤ 64, all D' ⊆ D): v_2(M_{DD'}) = K + κ(m, K) + R_m(D) − R_{m+K}(D') + γ(D∖D'); every entry of M is an integer.
- **G-L6 HELD, 798/798** (every I ⊆ [0, k), k ≤ 6, |I| ≤ 4, every r; exhaustive DP counting optimal matchings): the δ-optimal natural matching is unique and costs Σ_{L_r} ε.

### 3.3 Checks 2 and 3 — Bai and Gao et al. (engines/check23.py, logs/check23.log, VIGIA-FIN-OK) — HELD
**Check 2 (Bai, LAA 369 (2003) 251–261).** (a) **Bai's printed table** (p. 260, n = 2..11; «Reiner shares with the author the data computed by the Smith normal form program…»), transcribed by me from the rendered PDF page (`scratch/bai_p10-10.png`; in the original a multiplicity 1 is simply not printed, which is why pdftotext seems to «drop» it): **= the rule, 10/10**, and = my direct computation (§3.1). (b) **Thm 1.1** (2^{n−1} − 1 invariant factors): the rule gives 2^{n−1} − 1 non-trivial 2-factors and one Z for every n = 1..60 (60/60). (c) **Thm 1.3** (Z/2 count, generating function Σ a_{n+3}x^n = 1/((1−2x)(1−2x²)), p. 253 and p. 259): 58/58 for n = 3..60, and the closed form a_n = 2^{n−2} − 2^{⌊(n−2)/2⌋} for n = 2..60: 59/59. **Caveat (sealed with the prediction):** (b) and (c) are blind to the big clocks — (b) is automatic in the rule (each family contributes dim T(λ)/2 non-units) and (c) only counts small clocks (big clocks are ≥ k + 2^k ≥ 3); they test the multiplicities and the small clocks only.
**Check 3 (Gao–Marx-Kuo–McDonald–Yuen, arXiv:1912.06919v3, §4, p. 14 and p. 18).** **Thm 4.1** (top factor, max(max_{x<n}(v_2 x + x), v_2 n + n − 1)) and **Thm 4.2** (2nd..(n−1)th factors all equal max_{x<n}(v_2 x + x)): **the rule satisfies both for n = 2..30 (29/29 each) and for n = 31..64 (34/34 each).** The conjectures, for information: Conj 4.14 (n-th factor) n = 3..64: 62/62; the JMM poster's (n+1)-th factor n = 4..64: 61/61; Conj 5.4 at n = 4, 8, 16, 32, 64: 5/5.
**Controls.** The no-pooling rule violates Thm 4.1/4.2 from n = 6 on (20/29 and 18/29 hold): Gao's theorems do see the pooling. The carries-at-m rule satisfies both for every n ≤ 30: **Gao's theorems are blind to where the column ruler is read**; only check 1 (n = 6, 10–13) and check 4 see that ingredient.

### 3.4 Check 4 — L7 (Theorem F) by machine, my implementation of the construction (logs/p2_C4_63.log, p2_C4_64_127_a1.log, p2_C4_64_127_a234.log, p2_C4_128_255_a1.log, p2_C4_128_255_a234.log, p2_C4i0.log, p2_C4b.log, p2_PINT.log; all VIGIA-FIN-OK)
I chose L7 because it is the newest link, the one written fastest, and the one everything else rests on. My code builds, for every family λ ≤ 255 with |I| ≥ 1, every α = 1..4 and every m_low ∈ [0, 2^k) (86 360 houses), the houses H_0, …, H_n digit by digit, computes rulers, carry-out sets and gold **directly from the definitions** (not from the recursion), and checks at every level: the recursion formulas of 11.2.1–2 against the direct values; the walk formula ŷ_j = [max(X1, 0), min(X2, 0)] against my PAVA; Cut_j (the J-boundary and its mirror are real block starts); Λ_j; that F1 is a final segment; that the plumber's interval is non-empty; and (E), (M), (G) for the potential built with c_F at the **low end, the high end and the middle** of the interval (3 constructions per house, 259 080 in all). Then, in real cells i = 1..300 (λ ≤ 63, α = 1), i ≤ 4K + 1 (λ ≥ 64, α = 1) and i ≤ 2K + 1 (α ≥ 2), it checks the penalty form R_m = R − r_k(m)J, R_{m+K} = R − r_k(m+K)J and Theorem U's three conditions for v = V − P_r J, w = V − P_c J against the cell's own pooled clocks.
| check | passes | failures |
|---|---|---|
| recursion formulas (R, J, γ) | 873 816 levels | 0 |
| walk = PAVA | 873 816 | 0 |
| Cut_j | 436 908 | 0 |
| Λ_j | 873 816 | 0 |
| plumber's interval non-empty | 93 597 central flats | 0 |
| (E), (M), (G) | 873 816 each | 0 |
| penalty form of real cells | 686 169 | 0 |
| Theorem U in real cells | 686 169 | 0 |
| integer fit antitonic, ⌊μ_A⌋ ≥ ⌈μ_B⌉ for adjacent blocks | 1 559 985 sequences | 0 |
- **The i = 0 cell (λ ≤ 127, 120 families):** the valuations of M(λ, 0), rows D ≠ ∅, are one constant plus the base ruler of the house m_low = 2^k − 1 (120/120); the rule's i = 0 clocks (flight-1 form) are k + that constant + the pooled base clocks with the row ∅ cut off, and PAVA(x)[1:] = PAVA(x[1:]) (120/120); Theorem U holds on the i = 0 cell (120/120).
- **C4b, brute force (λ ≤ 30; i = 0..64, except λ = 30, 16 dancers, i = 0..12 for time, declared):** exact min-cost r-matchings on the true valuations of M give **T(r) ≥ Y(r) for every r in 1898/1898 cells**; the exact Smith form of M equals the rule (1898/1898); T(r) ≤ d_r (1898/1898).
- **Controls (each fires):** gold removed (γ := 0): (G) fails in 244 of 5 208 houses λ ≤ 63; the natural price c_F := v′(I′) breaks (M) or (G) in 24 houses; T(r) < U(r) (the unpooled partial sums) in 460 of the 1898 brute-force cells — the floor really needs the pooling.
- **P-INT:** my example x = (1, 2, 0, 1, 2, 2) has real blocks of means 3/2, 5/4 and integer split (2, 1, 2, 1, 1, 1): not antitonic. In every cell of the cube's families checked above the split is antitonic and adjacent blocks are separated by an integer.
So the link I trusted least survives a machine check written from my own reading, at three different prices of the interval, on every house λ ≤ 255. The scope sealed in S3 was met except for C4b's λ = 30, where I checked i ≤ 12 instead of i ≤ 64 (declared above and in §6).

## 4. Priority and credit


### 4.1 Is this the first statement of the whole 2-part of K(Q_n)? — **As far as I can find, yes.**
What the sources say (read in `material/sources/`, page and line of the original):
- **Bai 2003** (LAA 369), p. 253, last lines before §2: «The full structure of the Sylow-2 subgroup of the critical group of the n-cube is still unknown.» Bai proves Thm 1.1 (exactly 2^{n−1} − 1 invariant factors), Thm 1.2 (every odd Sylow), Thm 1.3 (generating function of the number a_n of Z/2's). The table on p. 260 (n ≤ 11) is Reiner's data from a Smith-form program, not a theorem.
- **Chandler–Sin–Xiang** (arXiv:1511.00272v2, 2015; the flights cite it as 2017, journal version not checked by me), §5.2 «Final remarks», p. 17: «We do not have any conjecture about its exact structure.» (their subject is the Smith group of the adjacency matrix, not the Laplacian).
- **Anzis–Prasad** (Reiner's REU 2016), p. 1: the determination of the 2-Sylow subgroup «remains an open problem»; they bound the largest factor.
- **Gao–Marx-Kuo–McDonald–Yuen** (arXiv:1912.06919v3; Comm. Algebra 2024, doi 10.1080/00927872.2024.2347582, confirmed by the search result tandfonline.com): Thm 4.1 and 4.2 (p. 14) give the top n − 1 factors; Conj 4.14 (p. 18); §5 (p. 19): «determining the complete structure still seems out of reach at this moment».
- **JMM poster 2019**: «the Sylow-2 subgroup remains a mystery»; «We have no conjectures for further factors» (beyond the (n+1)-th).
- **Reiner–Tseng** (arXiv:1301.2977v3) §12.2 re-derives Bai's odd-p result by double covers; nothing on the 2-part.
- **Ducey et al.** (arXiv:2310.09227v2, 2024): Smith and critical groups for the whole Bose–Mesner algebra of the **Johnson** scheme (subset intersection graphs), via Bier's P-matrix; nothing on the hypercube's 2-part.
- **Doty–Henke** (arXiv:math/0205186): decompositions of L ⊗ L′ for SL_2; nothing on sandpiles.
**Web searches (my queries and what they returned):**
1. «Sylow 2-subgroup critical group hypercube Q_n complete structure» (extended): Bai, Anzis–Prasad, Ducey–Jalil (arXiv:1308.2335), Gao et al. in Comm. Algebra; every summary says the 2-part is open.
2. «sandpile group of the hypercube 2-part tilting modules SL2 characteristic 2» (extended): only tilting-module papers (Tubbenhauer–Wedrich arXiv:1907.11560, Sutton–Tubbenhauer–Wedrich–Zhu «SL_2 tilting modules in the mixed case», Selecta 2023; Martin arXiv:1705.06980, 2004.01153); **no paper links tilting modules to sandpile groups.**
3. «multiplicity of tilting modules in tensor powers of natural module SL2 characteristic 2 recursion» (extended): **Larsen, arXiv:2405.16015 (2024)** — the fusion graph of V^{⊗2} at p = 2; Coulembier–Etingof–Ostrik–Tubbenhauer arXiv:2405.16786 (Contemp. Math. 829, 2025); Sheu arXiv:2512.24317.
4. «"critical group" OR "sandpile group" hypercube "2-Sylow" OR "Sylow-2" 2025 OR 2026 arXiv» (extended): only Gao et al. and older; arXiv:2506.09912 (extended sandpile groups, not the cube's 2-part).
5. «Reiner REU problem "Describe Syl_2 K" cube critical group 2-part solved»: Reiner's REU pages and a 2022 JMU undergraduate project (educ.jmu.edu/~duceyje/undergrad/2022/sherwocj_project.pdf), summarised by the engine as «there is still not even a conjecture of what the full 2-Sylow subgroup might look like». **I could not open it** (host not found; the web archive is refused to my fetch tool) — the same lead flight 4 could not open. Not read.
6. «Smith normal form Laplacian hypercube 2-adic elementary divisors representation theory modular tilting» (extended): CSX, Paley/Grassmann/Kneser papers of Sin, Xiang, Ducey; nothing on the cube's 2-part.
7. «critical group graph Laplacian "tilting module"… sandpile Smith normal form»: nothing connecting the two.
8. «Coulembier Etingof Ostrik Tubbenhauer fractal behavior…», «Tubbenhauer Wedrich quivers … T(1) tensor T(v)…»: tilting literature; no sandpiles.
9. «mathoverflow critical group hypercube Sylow 2 …»: same sources; open.
10. «"hypercube" Laplacian "Smith normal form" "divided powers" OR "Weyl module" OR "sl_2" 2-adic cokernel»: CSX only.
11. «integral lift of Frobenius twist SL2 lattice … Weyl module Δ(2m+1) divided powers construction»: nothing matching Φ (Weyl resolutions of Frobenius twists, twisted divided powers — different objects).
**Verdict.** No source I could read states, conjectures or proves the whole 2-part; the newest ones (Gao et al. 2024; Ducey et al. 2024) call it out of reach or do not touch it. Limits: summaries of a US-only search engine; one source unreachable; I did not search Google Scholar or MathSciNet. Absence of evidence is not proof.

### 4.2 Are Bai's and Gao's results credited correctly? — **Yes, with two small corrections**
- Bai: the flights credit him with the odd part (Thm 1.2) and Reiner's two conjectures (Thm 1.1: the number of invariant factors, which equals the number of 2-factors; Thm 1.3: the number of Z/2's): **correct**. Small correction: Bai's table (p. 260) is credited to Reiner's computer data in Bai's own text; the flights call it «Bai's table» (fine as a pointer, but it is data, not a theorem).
- Gao et al.: «its n − 1 largest factors» = Thm 4.1 (the largest) + Thm 4.2 (2nd..(n−1)th): **correct**. Conj 4.14 and 5.4 and the poster's (n+1)-th factor are conjectures there: the flights say so. FLIGHT4 §13 states they «follow from the closed rule by arithmetic that I have not done» for general n: **correct and honest**; they are proved only for the n where the rule was evaluated (my check 3: n ≤ 64; flight 3: n ≤ 261).
- **Credit not given (PRESENTATION/credit):** (i) the basis s_S = ∏(1 − x_i) in which the Laplacian becomes σ = U + 2D is the Laplacian analogue of CSX's monomial basis (CSX §5, eq. (5): adjacency = diag(n − 2|I|) + inclusion) and is Gao et al.'s change of variables u_i = x_i − 1 (proof of Prop 2.5); FLIGHT1 presents it as its own engine without citing either. (ii) The use of Bier's P-matrix to triangularise a Laplacian is also the first step of Ducey et al. 2024 (Johnson scheme); flight 1's Theorem B/Z are in that line (they are side results, not links of the final chain).

### 4.3 Nearest precedents — is the fusion recursion theirs? Is anything of ours in them?
- **Doty–Henke:** the fusion recursion is **not** in Doty–Henke (they treat L ⊗ L′ of two simples, Thm 2.1–2.7, and the twisted tensor factorisation of tilting modules, Lemma 1.4 — which is what the flights call Donkin's tensor product theorem and use to name T_dance(λ)).
- **The fusion recursion is known in substance:** Larsen (arXiv:2405.16015, 2024, §2) prints the fusion graph of V^{⊗2} at p = 2: V^{⊗2}⊗T(2n) ≅ T(2n+2) ⊕ ⊕_{i=1}^{r+1} T(2n+2−2^i)^{⊕2} (2^r ∥ n+1; T(0) terms omitted when n = 2^r − 1), citing Tubbenhauer–Wedrich for the characters. **My check P-LARSEN: iterating Larsen's rule gives exactly the flights' multiplicities for every even n ≤ 64 (32/32; control fires 32/32).** So the multiplicities m_λ(n) are standard (they also follow from Donkin's characters, my C-M0). The flights' form V⊗T(2l+2) = T(2l+1)² ⊕ Φ(V⊗T(l)) is a convenient reformulation; **what is new in L1/L2 is not the multiplicities but the integral statement RT′** (V^{⊗n}⊗Z_2 ≅ ⊕ T_dance(λ)^{m_λ(n)} as Dist_{Z_2}-lattices, with explicit lattices), which I did not find anywhere.
- **Ducey et al. 2023/24 (Johnson scheme):** same family of tools (Bier's basis, block triangularisation, diagonal forms over Z); different graphs; nothing of the tilting/dance/matching part.
- **Chandler–Sin–Xiang:** Bier's basis for the cube's adjacency matrix; the Laplacian 2-part explicitly left without conjecture.
- **Not found anywhere (to my search):** the integral Frobenius lift Φ, Theorem D's closed-form 2^{|I|}×2^{|I|} matrices, the deficit law, Theorem O, the carries form of the costs, and Theorem F. These are the new mathematics, if the audit holds.

## 5. Where I disagree with the auditor's audits
Read only after §0–§4 and §6–§8 were written (diary). Files: AUDIT_FIRST_PASS_FLIGHT_1/2/3, AUDIT_FLIGHT_4, BAI_2003_READING_v1, BARRIDO_NOVEDAD_TEOREMA_D_v1.
**Where I agree.** On every link I agree with the auditor's grade: RT′ (and the citation error FLIGHT3 found in FLIGHT2), Φ, P-R1, B.1, C.0, C.4, Theorem D, the cost form, Theorem O, Theorem U, Theorem F steps 1–8, base cell → real cells, i = 0. My independent code reproduces his G1 (my G-L5, 87 360 entries) and G3 (my C4: λ ≤ 255, α ≤ 4, three prices), with the same zero failures. On Bai, the reading and the table gate coincide with mine (his first transcription failed for the same superscript reason I avoided by reading the rendered page). On priority I reach the same conclusion by partly different searches.
**Where I disagree (four points):**
1. **Integer splitting (AUDIT_FLIGHT_4 §2, «Integer splitting — CORRECT. No two adjacent blocks have equal non-integer means…»).** Equal means are not the only way the integer split can fail to be antitonic: adjacent blocks of means 3/2 and 5/4 split as (2, 1 | 2, 1, 1, 1) (my P-INT). The property the proof needs is **⌊μ_A⌋ ≥ ⌈μ_B⌉ for adjacent blocks**; it is true, and the same induction gives it (integer shifts d_A ≥ d_B preserve it; the central block 0 has neighbours of mean > 0 and < 0; the junction without merge has μ ≥ 0), and it holds in every cell I checked (1 559 985 sequences). So the step is right, but the justification printed and accepted is too narrow: **PRESENTATION, not CORRECT as written.**
2. **The statement as printed (AUDIT_FLIGHT_4 §4, copied into MISSION §1).** It says the exponents of «Smith₂ M» are the integer PAVA of x_D. They are not: they are **k + 2^k + κ(i−1, 2^k) + PAVA(x)_D** (the k from 2^k·coker M, the rest from the constant valuation of the cell). The auditor's own G1 compares «up to ONE constant per cell», so the constant was seen and then dropped in the printed theorem; and the formula needs a separate convention at i = 0 (m = −1). The theorem is true; the one-line statement is not, read literally (§1, S1–S3).
3. **Doty–Henke as the source of m_λ(n) (AUDIT_FLIGHT_4 §5 «to credit»; BARRIDO Entry 2 «Larsen 2405.16015, Doty–Henke math/0205186: tilting decomposition of V^{⊗n}…»).** Doty–Henke decompose L ⊗ L′ for two simple modules and factorise tilting modules (Lemma 1.4); they do **not** give the multiplicities of T(λ) in V^{⊗n}. The right citations are Donkin's tensor product theorem (characters) and Larsen 2024 §2, whose V^{⊗2} fusion rule I checked to give **exactly** the flights' multiplicities (P-LARSEN, 32/32 even n ≤ 64; control fires). BARRIDO's conclusion «m_λ(n) known» is right; the attribution should move from Doty–Henke to Donkin/Larsen (and Tubbenhauer–Wedrich, whom Larsen cites).
4. **Credit for the basis (not in the auditor's list).** The basis s_S = ∏(1 − x_i), in which the Laplacian is σ = U + 2D, is the Laplacian analogue of CSX §5, eq. (5) (the adjacency matrix in the monomial basis is diag(n − 2|I|) + inclusion), and is Gao et al.'s change of variables u_i = x_i − 1 (proof of their Prop. 2.5). The auditor asks to credit Gao et al.'s method in general; I would name these two places.
**Small notes (no disagreement of substance).** (a) AUDIT_FLIGHT_4 §1 says «No external cold reading yet»: this report is one. (b) BARRIDO Entry 3 gives CSX as DCC 84 (2017); I did not verify the journal reference. (c) The auditor's chain table (§4) correctly omits Theorem Z; MISSION's table lists Bier's basis in L3, but it is not a link of the final chain (my L3).

## 6. Sealed predictions, hits and failures
| id | prediction (sealed time in checks/SEALED.md) | odds | ended |
|---|---|---|---|
| C-G0 | my Smith engine = PARI matsnf (random + Laplacians n ≤ 7) | 95 % | **held** 60/60, 7/7 |
| C-R0 | flight-1 form of the rule = mission form + my constant k + 2^k + κ(m, 2^k) (λ ≤ 63, 1 ≤ i ≤ 40) | 85 % | **held** 2520/2520 value by value; control (constant without κ) differs in 760 cells |
| C-M0 | fusion recursion = Donkin character peeling, n ≤ 64 | 97 % | **held** 64/64 (and Σ m_λ dim T(λ) = 2^n) |
| C1 | rule = direct Laplacian Smith form, n = 2..10 (and 11) | 90 % | **held** 10/10 (n = 2..11) |
| C1-ctrl-a | no pooling fails for some n ≤ 10 | 80 % | **held** (fires at n = 6 and n = 10) |
| C1-ctrl-b | carries at m fails for some n ≤ 10 | 90 % | **held** (fires at n = 6, 10, 11) |
| C1-count | 2^{n−1} − 1 factors and one Z, n = 2..10 | 99 % | **held** (n = 2..11) |
| C1-12-13 | rule = direct at n = 12 (S1) and n = 13 (S2) | 90 % | **held** 2/2 |
| G-L34 | dance lattices = small clocks + 2^k coker M = rule, λ ≤ 30, i ≤ 40 | 95 % | **held** 1230/1230; control fires 191 |
| G-L5 | closed-form valuations = ruler form, λ ≤ 63, i ≤ 64 | 95 % | **held** 87 360/87 360, all integral |
| G-L6 | Theorem O by exhaustive DP, k ≤ 6, |I| ≤ 4 | 97 % | **held** 798/798 |
| C4 | Theorem F's construction, λ ≤ 255, α ≤ 4, 3 prices, real cells, i = 0 | 90 % | **held**, 0 failures (table in §3.4) |
| C4b | brute-force floor and exact Smith, λ ≤ 30 | 95 % | **held** 1898/1898 (λ = 30 only to i = 12: scope reduced, declared) |
| C4-ctrl | (a) no gold fails, (b) natural price fails, (c) T < U somewhere | 85/70/95 % | **all fired**: 244 houses, 24 houses, 460 cells |
| P-INT | my example is non-antitonic (99 %); every cell antitonic and integer-separated (95 %) | — | **held** both |
| C2-table | Bai p. 260 = rule, n = 2..11 | 98 % | **held** 10/10 |
| C2-count | 2^{n−1} − 1 factors, n ≤ 60 (blind to big clocks) | 99 % | **held** 60/60 |
| C2-a_n | Z/2 count = Bai's generating function and closed form, n ≤ 60 (blind to big clocks) | 98 % | **held** 58/58, 59/59 |
| C3 | Gao Thm 4.1, 4.2, n = 2..30 (and 31..64) | 97 % | **held** 29/29, 29/29 (34/34, 34/34) |
| C3-conj | Conj 4.14, poster, Conj 5.4 to n = 64 | 90 % | **held** 62/62, 61/61, 5/5 |
| C3-ctrl | do the controls violate Gao? | 50 % | no pooling: **yes** (from n = 6); carries at m: **no** (blind) |
| P-LARSEN | Larsen's published V^{⊗2} fusion rule = the flights' recursion, even n ≤ 64 | 93 % | **held** 32/32; control fires 32/32 |

**Failures, in the same size of type:** none of my sealed predictions failed. One sealed scope was not met (C4b at λ = 30: i ≤ 12 instead of i ≤ 64). That every prediction held is itself a warning: most were predictions that the flights' claims survive my checks, at odds 90–99 %, so they could not surprise me much; the controls (each of which fired) are what show the checks could fail. Two checks are blind to the big-clock rule by construction (Bai's two counts), and one control (carries at m) is invisible to Gao et al.'s theorems; I said so when sealing or when reporting.

## 7. My errors
- **E1 (§1, first draft).** I wrote an example vector «λ = 6, i = 1 has x = (1, 0, 0, −1)» before computing it; by hand it is (1, 1, −1, −1). Corrected within minutes (diary line of the correction); the lesson: no number goes in the report before it is computed.
- **E2 (diary, G-L34 estimate line).** I wrote «1271 dance-lattice Smith forms» in the estimate; the run had 30 families × 41 shifts = 1230 cells. A miscount in the estimate only; corrected in the next diary line.
- **E3 (scope).** C4b was sealed for λ ≤ 30, i = 0..64; for λ = 30 (16 dancers, exhaustive DP over 2^16 column sets) I ran i = 0..12 only, for time. Declared in §3.4 and §6.
- **E4 (§3.1, first draft).** A garbled sentence about the n = 12 no-pooling control was written and corrected minutes later.
- **E5 (method).** My first C4 code (sets and tuples) would have needed far more than ten minutes for λ ≤ 255; I rewrote it with bitmasks **before** running it. No run was killed; every log ends in VIGIA-FIN-OK.
- **E6 (shell).** One here-document with non-ASCII text failed to parse as Python (encoding); the edit was redone from a script file (`scratch/edit_part5a.py`). Nothing was lost.

## 8. What I did not read
- **Not verified (side results, not links of the theorem):** FLIGHT1 Leg F (the hall of mirrors: catalogue, Theorem L / kiss matrix, K2, K3, N_lock), the fold law (D.4, P-F1..F3), Theorem B's controls; FLIGHT2 C.5–C.7 beyond what L6 needs; FLIGHT3 C.2–C.5 (Cauchy–Binet, salsa, St1, St2, the per-family machine check famcheck) and A.3 (Theorem A2) — superseded by Theorem F, read but not re-derived; FLIGHT4 A.1–A.8, §10 (the plumber P-F…P-F4) and the gold legs — superseded by §11, read but not verified.
- **Read but not redone by hand:** the E-side divided powers of Φ (FLIGHT2 A.1(b)); Kostant's commutation formula (standard, cited); FLIGHT2 C.5's Kummer bookkeeping u(D) − k = ρ_D + κ_{I∖D} + ε(D) (replaced by my gates C-R0, G-L5, G-L6, which check the equivalent statements).
- **Not opened:** the flights' engines (`material/engines_of_the_flights/`, by choice: my verdicts do not rest on them); the flights' SEALED files; Jantzen (not needed by RT′); the JMU 2022 project (unreachable); flight 4's `sources_4b/` (not in this folder).
- **Sources read only in part:** Gao et al. (statements of §1, §4, §5; not the proofs); CSX (§1–3, §5 start, §5.2); Doty–Henke (intro, §1–2 statements, §5 examples p = 2); Ducey et al. (abstract, §0–2 opening); Reiner–Tseng (abstract, §12.2); Anzis–Prasad (introduction). Bai: read whole.

## 9. Files with md5

(Sun Oct  4 20:06:45 CEST 2026; REPORT_COLD.md and logs/DIARY.md are not listed: they change as this list is written. material/ is untouched: its 121 files match MANIFEST_md5.txt, checked at the start. scratch/ holds my temporary files: the rendered Bai page, two matrix dumps, three edit scripts.)
```
d2abf544a007e95a4ea6617b334abd59 CLAUDE.md
ab96ce538f1671d50fec53acdadddea7 MISSION.md
e5f8cf13253222f0388fe7dab9edfe88 vigia.sh
dc3cdb7aa0813c0937ca31e82ed06b66 checks/SEALED.md
838cce703d5691a0ef61a55c62846c59 engines/check1.py
acb8ff3a7f1b7dee742399e0397fd4b1 engines/check23.py
4a68e64031369507adb07c5cebfc1387 engines/gate0.py
a2b0c30294928be20a91b298d7d7c1a0 engines/larsen.py
f18727b93705322325ed2d41d94396e2 engines/myrule.py
078bff932642d74175e9176dc588c922 engines/mysmith
06fa5ffb14898096f100af38b6d94c42 engines/mysmith.c
252b8c1677b6e2621e0c7a85f6e47384 engines/part2.py
976b8e16749fb0c707c34d629272a867 engines/rule_gates.py
2bd8d41461c0851d65a61fd69e546b99 logs/cc_mysmith.log
d967bde95e1031d0964844bccadf98de logs/check1_12_13.log
b210fe35fda0be3db50cf727c0c018ec logs/check1_2_11.log
a71194830a2ff1da4b0e39d7e7b66562 logs/check23.log
e8e56844996012162e0edc5a6caf524c logs/gate0.log
688135409fb58aadc980d7ec08c79807 logs/larsen.log
02b4b24257becb7f89067b30496911b2 logs/p2_C4_128_255_a1.log
73b6645ad181c4ec9f29b9e497df9d06 logs/p2_C4_128_255_a234.log
f5ee89bb49c028070b7f431217a9020f logs/p2_C4_63.log
0fd797f820ea45be807f6f79267e20e8 logs/p2_C4_64_127_a1.log
e01bb2f443a5679a83c3a74d09ddb975 logs/p2_C4_64_127_a234.log
980501b8cdef5294978733d2a99b7196 logs/p2_C4b.log
92ee87720322d882f7c87db9b5608d71 logs/p2_C4i0.log
c32a2a0b4593eb11bc4add7123c2e37d logs/p2_L34.log
6b2adcb00628941266335e3a74040ea0 logs/p2_L5.log
7cc6196d1a6ac4c9acd8e85dcf2d9598 logs/p2_L6.log
855d087adf5d8e1a67d5fa49a8d6a8dc logs/p2_PINT.log
2046fdd3b17b5c980d7a14c0ad567e69 logs/rule_gates.log
586032899451aa6d5dbd5947259a97e4 scratch/bai_p10-10.png
6419798863860832f8cb50a01a251a18 scratch/edit_part5a.py
60f5855d57e584e048fd81d125191bce scratch/edit_part5b.py
ec71c5bc7e2d25358c2e3a183e05403d scratch/edit_part5c.py
12ecec2ca27dc5767c56bd378ae676b3 scratch/g0_mat.txt
58351122f5e6070aac5f2a2feb044720 scratch/md5_block.txt
baada8e89960f417ff3a4bb9b9f9409a scratch/p2_mat.txt
```
(Note: the line for scratch/md5_block.txt is the md5 of that file while it was still being written — a self-reference slip; ignore that one line.)
