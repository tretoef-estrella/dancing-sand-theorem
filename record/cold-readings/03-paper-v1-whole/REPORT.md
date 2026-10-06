# REPORT_COLD — «The Dancing Sand Theorem», version 1

Cold reader: «Grepy el lector frío del cubo 3». Mission: `MISSION.md`.

## 0. First line

- Does the paper hold as written: **HOLDS WITH GAPS**
- Is it ready for submission: **AFTER CORRECTIONS**

Summary (details and line numbers in §2–§6):
1. **All the claimed theorems are true as far as I can tell, and I re-derived every numbered statement of §2–§10
   and the assemblies §8, §10.8 in my own words.** Theorem O (the new top-bits proof) is correct and proves
   uniqueness; §10 (rigidity 10.12, cleanliness 10.15 with the rings `𝒦`/`𝒮`, odd and even families, both continuity
   steps at `i = 0`) is correct and every hypothesis of 10.12 is supplied by 10.15; §9 says exactly what Gao et al.
   conjectured, in their notation.
2. **One gap in a proof (§7):** the integer part of Lemma 7.2(b) is **false as stated** (counterexample
   `x = (3,4,3,4)`, cut at 2, `δ = (1,1,0,0)`), and it is used in Theorem F step 1, Lemma 7.9, Theorem 7.10 (U2), the
   `i = 0` deletion and Prop. 9.5 (H). The conclusions survive: a *strict* (Cut) — provable by the same induction,
   sketched in §2 — makes every application legitimate, and my straddle detector finds no violation in all 43 690
   houses with `k ≤ 7`, `α ∈ {1,2}`.
3. **Numbers:** the rule of §1.2, written from §1 alone, equals the 2-adic Smith form of `L(Q_n)` for `n = 1..12`;
   the fold law holds for `n = 1..12`; per family, Theorem D + Theorem 7.10 hold for `α = 1, 2` far beyond the cube
   range (7 874 matrix cells, 1 401 lattice cells), and `X̄(λ,i) ≅ 2X(λ,i)` for `λ ≤ 63`, `i ≤ 8`; the formal dance of
   §10 behaves as proved for `l ≤ 31`; Gao et al.'s Table 1 (`n ≤ 11`), OEIS A193134, Larsen's fusion rule and the odd
   part of Corollary 1.4 all agree. Every control I built fails where it must.
4. **Wrong or overstated side claims:** «`M` has at most `(λ+1)/2` rows» (false for `λ = 2^{k+1}−2`); Remark (2) of
   §10.5 / §12.2 (cleanliness failing at `l = 31`, `63`) **not reproduced**; §12.2 «Theorem 6.2: all `I` with
   `|I| ≤ 4`» is really `|I| ≤ 3` in the auditor's gate; 13/26 rows of §12.2 have no control; several rows rest on
   code not provided; §1.0/§13 grade Theorem O and the §10 organization «read cold» although their printed proofs are
   new (§12.3).
5. **Citations:** quotations exact, except a typo silently corrected inside quotation marks (IKKY) and a
   **misleading ellipsis in the [Aky26] quotation** that removes «with fixed vertices», after which the paper claims
   the fold law answers their question — the antipodal fold is precisely the fixed-point-free case they set aside.
   No priority problem found.
6. **Writing:** heavy symbol overloading (`τ, κ, σ, φ, ε, h, c, a, …`), one undefined `J`, `𝔞` rendered as `a` in the
   pdf, several formulas broken across lines (the exponent in Corollary 1.7), matrices typeset as nested lists, and
   process narrative (§12–§13) unusual for a journal. Honest about AI use and the absence of a human referee.

## 1. The claims as I read them

(Read from the title, abstract and §1 of the paper only, lines 1–170, before §2.)

**C1 — Main Theorem.** For every n ≥ 1, `Syl_2 K(Q_n) ⊕ Z_2 ≅ ⊕_λ X(λ, (n−λ)/2)^{m_λ(n)}` over the families
`1 ≤ λ ≤ n`, `λ ≡ n (2)`, with `m_λ(n)` given by a three-line recursion (identified in §3 with tilting
multiplicities in `V^{⊗n}`) and `X(λ, i)` = «small clocks» `⊕_{a<k}(Z/2^a)^{2^{|I|+k−1−a}}` ⊕ «big clocks»
`Z/2^{ŷ_i(D)}`, `D ⊆ I`, where `ŷ` is an integer rounding of the antitonic least-squares fit of the raw clocks
`u_i(D) = φ(ξ_D) + κ(i+o_D−1, ξ_D) + h(D)`. The rule is a finite computation with binomial valuations.

**C2 — Theorem D** (§4): each family reduces to small clocks plus `coker(2^k M(λ, i))`, `M` a `2^{|I|}`-square
explicit triangular matrix. **C3 — Theorems O and F** (§6–§7): Smith form of `M` = pooled clocks, upper bound for
the determinantal divisors from one minor with a unique cheapest matching (O), lower bound from a potential (F,
via U).

**C4 — Theorem DW (fold law).** `Syl_2 K̄(n) ≅ 2·Syl_2 K(Q_n)` for every n ≥ 1, `K̄(n)` the sandpile group of
`Q_n/⟨𝟙⟩` (= `FQ_{n−1}` of the interconnection literature). Equivalently `Syl_2 K(Q_n) = (Z/2)^{a_n} ⊕ (Syl_2 K̄(n)
raised by one)`, `a_n = 2^{n−2} − 2^{⌊(n−2)/2⌋}`.

**C5 — Corollary 1.4.** Whole sandpile group of the folded cube: 2-part from C1 + C4; odd part
`Syl_p K̄(n) ≅ Syl_p ⊕_{j even ≥ 2}(Z/2j)^{C(n,j)}` from [GMMY24, Prop. 1.9].

**C6 — Corollaries 1.5–1.7.** Bai's counts (`2^{n−1} − 1` cyclic factors, `a_n` of them `Z/2`); the `n + 1` largest
factors in three cases (recovering [GMMY24, Thms 4.1, 4.2], proving [GMMY24, Conj. 4.14] and the `(n+1)`-th
factor of the poster [GMM19]); `Syl_2 K(Q_{2^e}) ≅ Syl_2 K(Q_{2^e−1})^2 ⊕ Z/2^{2^e+e−1}` ([GMMY24, Conj. 5.4]).

**C7 — Priority (§1.7).** New: C1; the tilting decomposition of a sandpile group; the proofs in C6 of the two
conjectures and the poster formula; C4–C5; the proof techniques. Not new: odd part (Bai), largest factors and
odd parts of Cayley graphs of `F_2^r` (GMMY), the monomial basis (GMMY, CSX), tilting multiplicities (Donkin,
TW21, Larsen), standard tools.

**C8 — Status (abstract, §1.0).** Not refereed by a human expert; each proof re-derived by a non-author reader;
Main Theorem and Theorems D, O, F, DW read cold before; the whole text never read cold.

First-reading remarks on §1 (details in §2 and §5 of this report):
- The claims are mutually consistent: I checked by hand that the three cases of Corollary 1.6 agree with the
  «in particular» forms (for n even `g(n) = g(n−1)` because `φ(n−2) ≥ n−1`; for n odd `g(n) = max(G, φ(n−1))`),
  and that the dimension count `Σ m_λ(n)·2^{|I|+k} = 2^n` holds in the n = 6 example.
- The mod-2 remark of §1.3 is a correct deduction from C4 plus Bai's count: my Smith forms give F_2-rank of the
  folded Laplacian `= a_n` for n ≤ 12 (valuation-0 count; e.g. n = 5: 6).
- The «A naming trap» paragraph agrees with my own reduction: `Q_n/⟨𝟙⟩` = Cayley graph of `F_2^{n−1}` with
  `e_1,…,e_{n−1}, 𝟙` (double edge at n = 2).

## 2. Statement by statement (§2–§10, and the assemblies §8 and §10.8)

Format of each item: **statement in my words** · **verdict** · where a doubt lives · external facts used.

#### §2 The group ring as a module over the hyperalgebra

- **§2.1 setup.** Laplacian of `Q_n` on `Z^G = R = Z[G]` is multiplication by `σ = Σ(1 − x_i)`; the `s_S` are a
  Z-basis. · **HOLDS** (I checked `σ·Σ f(g)g = Σ_h (n f(h) − Σ_i f(x_i h)) h`, `x_i = x_i^{−1}`). · External:
  `coker L = Z ⊕ K` for connected G (standard, [Lor91], [Big99]) — correct use.
- **Lemma 2.1** (`s_j s_S = s_{S∪j}` or `2 s_S`; `σ = U + 2D`). · **HOLDS** (`s_j^2 = 2 − 2x_j = 2s_j`).
  · PRESENTATION, line 183: «`Syl_2(Z ⊕ K) ⊗ Z_2 = Z_2 ⊕ Syl_2 K`» — `Syl_2` of the infinite group `Z ⊕ K` is not
  defined; what is meant is `(Z ⊕ K) ⊗ Z_2 ≅ Z_2 ⊕ Syl_2 K`. The conclusion (`coker(σ on R⊗Z_2)`, by right
  exactness of `⊗`) is right. I also confirmed numerically that `U + 2D` and `L(Q_n)` have the same 2-adic
  Smith form (both give the rule) — implicitly, since my check 3.1 used `L` directly.
- **§2.2 definitions** (Kostant form, (K), lattice, floor grading, `V`). · **HOLDS** as definitions. (K) is
  [Hum72, §26.2 Lemma] / [Kos66]: the formula printed agrees with the standard one
  `x^{(c)}y^{(b)} = Σ_k y^{(b−k)} binom(h−b−c+2k, k) x^{(c−k)}` — correct. · Doubt (PRESENTATION, line 191):
  «`H` acts diagonally … each weight space is then a direct summand» — «then» suggests a deduction; with
  «diagonally» read as `X = ⊕_w X_w` it is a tautology. Say «X is the direct sum of its weight spaces».
- **Lemma 2.2** (dictionary `s_S ↦ b_1` at `S`; `U ↦ F`, `D ↦ (n−H)/2`, `σ = F + n − H`). · **HOLDS** (F acts on
  `V^{⊗n}` through the iterated coproduct; `F^{(r)}` acts as the sum over r-subsets because `F^{(≥2)} = 0` on `V`).
- **Corollary 2.3** (the cokernel splits along any `Dist_A`-decomposition of `V^{⊗n}`). · **HOLDS** (σ lies in the
  image of `Dist_A`).
- **§2.3 Weyl and dual Weyl lattices, the anti-involution `ι`, contravariant dual.** · **HOLDS**: I re-derived
  `E e_r = (λ−r+1) e_{r−1}` from (K) with `s = 1`, `F w_r = (λ−r) w_{r+1}`, `E w_r = r w_{r−1}` from the dual
  pairing, the left-module property of `X^ι`, `Δ∘ι = (ι⊗ι)∘Δ`, `V^ι ≅ V`.
- **Lemma 2.4** (`Δ_A(m) ⊗ V`: sub `Δ_A(m+1)`, quotient `Δ_A(m−1)`; dual statement). · **HOLDS**. The vectors
  `F^{(r)}(v⊗b_0) = F^{(r)}v⊗b_0 + F^{(r−1)}v⊗b_1` each carry coefficient 1 on a distinct basis vector, so they
  span a saturated sublattice; `E^{(s)}(v⊗b_1) = E^{(s−1)}v⊗b_0 = 0` for `s ≥ 2`, `F^{(s)}(v⊗b_1) = F^{(s)}v⊗b_1`
  exactly (not only modulo `X_1`, as the text says — harmless). The identification «free with the character of
  Δ(m+1) and generated by a highest weight vector ⇒ ≅ Δ_A(m+1)» is compressed: the clean argument is that
  `X_1 ⊗ Q` is the simple module of highest weight m+1 and `X_1 = Dist_A·(v⊗b_0)` corresponds to `Dist_A·v'`.
  GAP-free in substance; PRESENTATION (one sentence).

#### §3 The dance lattices and the family decomposition

- **Proposition 3.1** (the doubling functor `Φ(N) = b_0⊗N ⊕ b_1⊗N`). (a) lattice, exact, preserves saturation;
  (b) closed formulas for `F^{(r)}`; (c) `Φ(N)⊗F_2 ≅ V ⊗ N̄^{[1]}`; (d) `Φ(Δ(μ)) ≅ Δ(2μ+1)`, `Φ(∇(μ)) ≅ ∇(2μ+1)`.
  · **HOLDS.** I re-derived: `[E,F] = 2w+1` on `b_0n` and `= 4w − 2w − 1` on `b_1n`; `F^{2s}(b_0n) = 2^s b_0F^sn` etc.
  and the odd denominators `(2s∓1)!!`; `Ω = 4FE + (H+1)^2` is (twice the Casimir plus one) central and integral;
  `E^{2}(b_1n) = 2(Ω − w^2) b_1En`, `E^{3}(b_1n) = 2(Ω−(w+2)^2)(Ω−w^2) b_0En` agree with the printed products;
  mod 2 the products are odd scalars; the twist formulas of `V⊗M^{[1]}` by the coproduct; in (d) the recursions
  `c_{2s} = (2μ+1−2s)c_{2s+1}`, `c_{2s+1} = c_{2s+2}` (∇) and ratios `2s+1`, `1` (Δ). · Doubt: none of substance.
  (d) uses that a finite-dimensional `U_Q`-module with the character of `Δ(2μ+1)` is simple — Weyl's complete
  reducibility in characteristic 0; not stated (PRESENTATION, see Remark (2) below).
- **Lemma 3.2 (Lemma W)** (extension by `Δ_A(λ)` of a lattice with weights in `[−λ, λ]` splits). · **HOLDS**:
  `E^{(s)}F^{(r)}x = C(λ−r+s, s)F^{(r−s)}x` from (K) because only `j = s` survives, and the sum is empty when `s > r`.
  · External: (K) — correct use.
- **Lemma 3.3** (`Ext^1(Δ_A(λ), ∇_A(μ)) = 0`; consequences). · **HOLDS.** Case `μ ≤ λ` by Lemma W, case `μ > λ`
  by `ι`-duality; dévissage; the sequence `0 → N →2 N → N̄ → 0`. · Small GAP of exposition, line 246: «an
  extension of two lattices is a lattice» needs that the extension is a weight module: true because `X ⊗ Q` is
  semisimple (Weyl) and the weight projections are integer-valued polynomials in `C(H, r)` (interpolation in the
  binomial basis on a finite set of weights). One sentence would close it.
- **Corollary 3.4** (two lattices with both filtrations and isomorphic reductions are isomorphic). · **HOLDS**
  (`gf = 1 + 2h`, `h = (gf−1)/2` is again a `Dist_A`-map because `X` is torsion-free; the Neumann series converges).
- **§3.3 definition of `T(λ)`; rank, weights, character.** · **HOLDS** (induction: `Φ` scales exponents by 2 and
  multiplies by `e + e^{−1}`, which shifts `k` and `I` by one and adds the `t = 0` factor to the `t < k` product;
  `V⊗Φ` adds `0` to `I`; top weight `= 2^k − 1 + Σ_{t∈I} 2^t = λ`, once). Both kinds of filtration are preserved by
  `Φ` (3.1(a),(d)) and by `V ⊗ −` (Lemma 2.4, exactness, refinement) — HOLDS.
- **Lemma 3.5** (`V^{⊗3} ≅ Δ(3) ⊕ V^2`, `Δ(3) ≅ V⊗V^{[1]}` over `F_2`; consequence for `V⊗V⊗Φ(N)`). · **HOLDS**:
  form values `1,3,3,1`; `W^⊥` has weights `±1` with 2-dimensional weight spaces; `EF = H = 1` on its weight-1
  space; `F^{(2)}(b_0⊗b_0) = b_0⊗b_1` in `V⊗V^{[1]}`; the twist is monoidal (only even divided powers survive in the
  coproduct). · PRESENTATION: Lemma 3.2 is stated over `A` but applied over `F_2` (its proof works verbatim); and
  what is used is the universal-property part of its proof (`φ(e_r) := F^{(r)}x`), not the splitting statement.
- **Theorem 3.6** (`V^{⊗n} ⊗ A ≅ ⊕ T(λ)^{m_λ(n)}`). · **HOLDS** (double induction, on `n` and on `l` inside
  `V·[2l+2]`; Lemma 3.5 + Corollary 3.4 for the only non-definitional case). · External: none beyond (K) and
  completeness of `Z_2` — plus Weyl's theorem over Q (see above).
- **Remarks after 3.6.** (1) Donkin's tensor product theorem for `p = 2` gives `T(1)⊗T(μ)^{[1]} ≅ T(2μ+1)` and
  `T(2)⊗T(μ)^{[1]} ≅ T(2μ+2)`, consistent with the definitions; stated as not used — correct. The claim about
  Larsen's fusion rule is checked in §4 of this report. (2) «only (K), Lemma 3.2 and the completeness of `Z_2`» is
  slightly too strong: Weyl's complete reducibility over Q is also used (3.1(d), 3.3). PRESENTATION.
- **Lemma 3.7** (`m_0 = 0`, `m_n(n) = 1`, `m_1`, `m_2`). · **HOLDS** (I re-derived the three production facts).
- **§3.4 and Theorem 3.8** (`Z_2 ⊕ Syl_2 K(Q_n) ≅ ⊕ X^{(1)}(λ, (n−λ)/2)^{m_λ(n)}`). · **HOLDS** (`σ = F + (λ−H) +
  (n−λ)` on a summand; the parity and range of λ follow from weights and `m_0 = 0`).

#### §4 The dance: Theorem D

- **§4.1 payment systems.** Definition; `σ^{(α)}_i` is an even payment system of size 1. · **HOLDS** (definition).
- **Proposition 4.1 (doblar)** (`coker G ≅ coker 2G'` on `Φ(N')`, with the printed `π'`, `K'`). · **HOLDS.** I redid
  the substitution: after eliminating the unit pivots `b_1nι_{s'}`, `G(b_1nι_{s'})` becomes
  `2b_0(Fn)ι_{s'} − π_{s'}(2f+1)π_{s'}(2f) b_0nι_{s'} − Σ_u[π_{s'}(2f+1)K_{us'}(2f) + K_{us'}(2f+1)π_u(2f) +
  Σ_{s'<s<u}K_{ss'}(2f+1)K_{us}(2f)] b_0nι_u`, exactly as printed. Each pivot vector occurs in exactly one
  eliminating relation, so the quotient is `(b_0⊗N')^{⊕r}`. Evenness preserved.
- **Proposition 4.2 (paso)** (`V⊗Φ(N')`, basis `A, B, C, Dd`, size doubles, printed `π''`, `K''`). · **HOLDS.** I
  checked the four `F`-formulas from the coproduct, the floors `2f, 2f+1, 2f+1, 2f+2`, both substitutions (the
  `C`-relation gives the doblar formula shifted to `(2f+1, 2f+2)`), the two new couplings `(s',A)→(s',C)` and
  `(s',A)→(u,C)`, and that the lexicographic slot order is a linear extension of inclusion of dancers.
- **Proposition 4.3** (after `k` moves: small clocks ⊕ `coker(2^k M)`). · **HOLDS.** Unit-pivot elimination gives
  `G ~ I ⊕ 2G'` (Schur complement), hence `2^hG ~ 2^hI ⊕ 2^{h+1}G'`; ranks `2^{k+|I|−h}`; count of factors
  `2^{|I|}(2^{k−1}−1) + 2^{|I|} = 2^{|I|+k−1}`. · PRESENTATION: the slot order produced by the pasos is NOT the
  o-order (for `I = {0,1}` it is `∅, {1}, {0}, {0,1}`); this is harmless (both extend inclusion; Smith form is
  order-free) but the sentence «we index M by dancers» should say that the o-order is a re-indexing.
- **Theorem 4.4 (windows)** (closed form of `M_{DD'}` through `q_k`). · **HOLDS.** I re-derived the induction: in
  each of the three doblar terms and in the two paso couplings the two windows are adjacent and their union is
  the level-`h+1` window of the new pair; the coefficients add up to `−½[(c^{(h)})^2]_{D∖D'}` and `−x_hc^{(h)}`;
  the substitution `y_t = 2^{2^t}x_t`, `c^{(h)} = −2^{1−2^h}q_h` gives `q_0 = −1` and the printed recursion;
  window size `K − o(D∖D') ≥ K − o_I ≥ 1`. Integrality: `v_2(M_{DD'}) ≥ 1 − K + o + α(K − o) ≥ 1`.
- **Lemma 4.5 (deficit law)** `v_2 a_k(Δ) = k − |Δ| − min Δ`. · **HOLDS** (induction on `|Δ|` then `t`; the cross
  terms exceed by `t − max Δ ≥ 1`). Small remark: for `Δ = {0}` one gets `a_1({0}) = −a_0(∅) = +1`, not `−1` as the
  proof says («This is −1 if Δ = {m}» is true only for `m ≥ 1`); the valuation is unaffected. PRESENTATION.
  Strict subadditivity `δ(Δ_1)+δ(Δ_2)−δ(Δ_1⊔Δ_2) = k − max(min Δ_1, min Δ_2) ≥ 1` — HOLDS.
- **Theorem D** (Prop. 4.3 + Thm 4.4 + Lemma 4.5; valuation formula of the entries). · **HOLDS.** The `λ = 6`
  example matrix: I recomputed `q_2 = 1 + 2y_0 − y_1 − y_0y_1` and all nine entries — correct.
- **Closing remark of §4.5**, line 376: «The matrix `M` has at most `(λ + 1)/2` rows». · **ERROR (minor, in a
  remark):** `M` has `2^{|I|}` rows, and when every digit of `λ+1` below the leading one is 1 (`λ = 2^{k+1} − 2`)
  this is `2^k = (λ+2)/2 > (λ+1)/2`; e.g. `λ = 2`: 2 rows, `(λ+1)/2 = 1.5`. Correct bound: `⌊λ/2⌋ + 1`. Nothing
  depends on it.

#### §5 The valuations: rulers, gold and clocks

- **Definitions** (ruler `R_μ(E)`, gold `γ(Δ)`, clocks of the cell `x_D`; they depend on `α`). · **HOLDS** (for
  `α = 1` they are those of §1.2).
- **Lemma 5.1** (a) `δ(Δ) = Σ_{t∈Δ}(h_t − 1) + γ(Δ)`; (b) `γ(Δ) = 0` iff `Δ` is empty or a tail of `I`. · **HOLDS**
  (telescoping `k − min Δ = Σ_{t∈I, t≥min Δ} h_t`).
- **Proposition 5.2 (cost form)** `v_2(M_{ab}) = αK + κ(m,K) + R_m(a) − R_{m+K}(b) + γ(a∖b)`. · **HOLDS.** I redid it:
  Legendre gives `Σ_{d=x}^{y−1} v_2(m+1+d) = (y−x) − s_2(m+y) + s_2(m+x)`; with
  `R_μ(E) = G(E) − αo_E + s_2(μ+o_E) − s_2(μ)` and `δ(Δ) = G(a) − G(b) + γ(Δ)` the difference is
  `1 + αK + s_2(m) − s_2(m+K) = αK + κ(m,K)`. · External: Legendre's formula — correct use.
- **Proposition 5.3** (`u_i(D) = k + K + κ(m,K) + x_D`, `α = 1`, `i ≥ 1`). · **HOLDS**, by hand and by machine (my S6:
  363 600 triples, 0 mismatches). Step 1: the carry stretches `[t+1, next(t)]` are disjoint and stop at a position
  of `I ∪ {k}`, so `s_2(μ) = (k − |I|) + |E| − G(E)`; the final «difference» is printed with the opposite sign of
  what one computes (`k − |I| − G(D) − G(E) − t_1`), harmless since it is 0. Steps 2–3: the cocycle identity of `κ`.
- **The shift `i = 0`.** Only the entry `(∅, ∅)` of `M(λ, 0)` vanishes (it is the whole row `∅`, the matrix being
  lower triangular); no other window contains `d = 0`. · **HOLDS.** · PRESENTATION, line 416: «it is the cost form
  of the **house** `m = K − 1` read at `m` on both sides» is a forward reference to §7.3 that a reader cannot parse
  here. Note for later (§8): with a zero row the cokernel at `i = 0` is `Z_2 ⊕ coker` of the
  `(2^{|I|}−1) × 2^{|I|}` matrix of the other rows, which keeps the column `∅` — to be checked in §6–§8.
- **Proposition 5.4** (cost form and clocks at `i = 0`; `κ(K−1, o_E) = k − min E`). · **HOLDS** (`s_2(o_E − 1) =
  |E| − 1 + min E`; `κ(o_D − 1, ξ) − κ(o_D, ξ) = v_2(o_D) − v_2(o_D + ξ) = min D − min E`). · PRESENTATION, line
  422: the symbol `J` («since `J − 1 = o_D − 1` replaces `J − 1 = o_D`») is never defined; it stands for
  `i + o_D` (the first argument of `κ` in `u_i(D)` is `J − 1`).

#### §6 The Smith form of M: the ceiling (Theorem O — read hardest)

- **§6.1 setup** (`d_r` = sum of the `r` smallest exponents; o-order, `L_r`, `F_r = {I∖D : D ∈ L_r}`; `d̂_r`, `T(r)`,
  `U(r)`, `Y(r)`). · **HOLDS** (`D ↦ I∖D` reverses the o-order because `o_{I∖D} = o_I − o_D`). External: Smith
  form over a DVR and determinantal divisors — standard, correct.
- **Lemma 6.1 (tropical bound)** `d̂_r ≥ T(r)`. · **HOLDS** (ultrametric inequality on the Leibniz expansion; every
  support entry has the exact valuation of Prop. 5.2).
- **Theorem 6.2 (Theorem O)**: for every `I` and `0 ≤ r ≤ N` there is exactly one bijection `L_r → F_r` with all
  arrows golden. · **HOLDS — re-derived in my own words, the proof is complete and shows uniqueness.** My version:
  with `p(D) ∈ [0, 2^s)`, the golden images of `p` are `p` and `p` with a non-empty all-ones block of top bits
  cleared; so (i) a column whose top bit is 1 can only be reached by a loop; (ii) a row whose top bit is 0 can only
  go by a loop. For `r ≤ N/2` all rows have top bit 1 and all columns top bit 0, so every arrow clears the top bit
  and the golden images of `1p'` with top bit 0 are exactly `0q'` with `q'` a golden image of `p'` in `s−1` bits:
  solutions correspond bijectively to those of `(s−1, r)`. For `r = N/2 + q` the loops on `[N/2, N/2+q)` (forced
  by (i)) and on `[N/2−q, N/2)` (forced by (ii)) are both rows and columns; the remaining rows `[N/2+q, N)` and
  columns `[0, N/2−q)` can only be joined by top-bit-clearing arrows: problem `(s−1, N/2−q)`. Edge cases `r = 0`
  (empty map) and `r = N` (identity) are covered. The induction is on a purely combinatorial statement about
  bit strings, so it does not need the smaller problem to come from a smaller `I` — correct as written.
  Machine check of uniqueness: see §3.3 of this report.
- **Corollary 6.3 (natural minor)** `v_2 det M[L_r, F_r] = r(αK + κ(m,K)) + U(r)`, hence `d̂_r ≤ U(r)`. · **HOLDS**
  (row and column terms of the cost form do not depend on the bijection and sum to `U(r)`; gold ≥ 0 with equality
  only for `σ_r`; all support entries are non-zero for `i ≥ 1` because `i + d ≥ 1` and `a_k(Δ) ≠ 0`).
- **Lemma 6.4 (convexity)**: convex `d` with integer increments, `d(0) = 0`, `d ≤ U` ⇒ `d ≤ Y`. · **HOLDS.** Both
  cases redone: in the second case the increment `≤ q` in `(r^*, r_1]` exists because
  `d(r_1) − d(r^*) < Y(r_1) − Y(r^*) = (r_1 − r^*)(q+1)`; the text says «some increment … is at most q» without
  this one-line reason (PRESENTATION). The lemma depends on the convention that inside a block the `⌈S/p⌉` copies
  come first in o-order — consistent with §1.2.
- **Theorem 6.5** (`T ≥ Y` and `ŷ` non-increasing ⇒ exponents `= αK + κ(m,K) + ŷ_D`). · **HOLDS** (sandwich
  `Y ≤ T ≤ d̂ ≤ Y`). Scope: `i ≥ 1` only — `M(λ, 0)` is singular; where the shift 0 is treated is checked in §7.5/§8.

#### §7.1–§7.3 Antitonic fits, Theorem U, houses

- **Lemma 7.1 (characterization of the antitonic fit).** · **HOLDS** (perturbation for necessity; Abel summation
  `Σ(x_j − c)(c − y_j) = −Σ S_s(y_s − y_{s+1}) ≥ 0` for sufficiency). External: projection onto a closed convex cone.
- **Lemma 7.2 (cuts and shifts).** (a) **HOLDS.** (c) **HOLDS.** (b) the real statement `fit(x+δ) = fit(x)+δ`
  **HOLDS**, but the sentence «the level sets of `fit(x)` … are the level sets of `fit(x)+δ`» and the **integer
  statement are FALSE as stated** — a level set of `fit(x)` may straddle a cut (cut at `b` allows equal values on
  both sides), and a jump of `δ` there splits it, which changes the integer rounding. Counterexample, machine
  checked (`engines/lemma72b_counterexample.py`, `logs/lemma72b_counterexample.log`): `x = (3,4,3,4)` is cut at
  `b = 2` (all fits are `7/2`), `δ = (1,1,0,0)`; integer fit of `x+δ` is `(5,4,4,3)`, integer fit of `x` plus `δ`
  is `(5,5,3,3)` — different multisets. Control `δ = (1,1,1,1)` gives equality. The repair is easy (require that
  `δ` be constant on every level set of `fit(x)`, i.e. that the cuts where `δ` jumps separate level sets, or that
  the straddling level sets have integer value). **Verdict: ERROR in the statement of Lemma 7.2(b) (integer
  part); whether it infects Theorem F depends on how 7.2(b) is applied — see §7.4 below.**
- **Antisymmetry paragraph** (fit and integer fit of an antisymmetric sequence are antisymmetric). · **HOLDS**
  (`(−S) mod p = p − (S mod p)` and `⌈−S/p⌉ = −⌊S/p⌋`).
- **Lemma 7.3 (antisymmetric gluing).** · **HOLDS** (I redid the three kinds of prefixes of the central level set
  `P ∪ P^*`; `X_1 ≤ 0` where `Z_1 ≤ 0` because `⌈c⌉ ≤ 0` for `c ≤ 0`).
- **Theorem 7.4 (Theorem U)** (dual certificate `v, w` ⇒ `T(r) ≥ Y(r)`). · **HOLDS** (LP-duality-type argument).
- **§7.3 houses, penalty cells; Lemma 7.5 (real cells)** `R_m = R_H − r_k(m)J_H`. · **HOLDS** (carries of `m + o_E`
  = carries of `ℓ + o_E`, plus `r_k(m)` more when a carry leaves bit `k−1`). Remark (mine): one of `r_k(m)`,
  `r_k(m+K)` is always 0 (bit `k` of `m` is 1 in exactly one of `m`, `m+K`) — the text never says it; useful.
- **Lemma 7.6 (the gates).** · **HOLDS** (case analysis of carries inside `W_t`, including `d + c_t = 2`; no carry
  is born below `t_1`; the carry out of bit `k−1` is counted in the last window).
- **Lemma 7.7 (the top digit).** · **HOLDS** (windows of `I'` unchanged because the predecessor of `c` has
  `next = c` in both houses; `c_c(E) = J_{H'}(E ∩ I')`; the γ-relations; `d_1` by subtraction).

#### §7.4 Theorem F, §7.5, and §8 (the assembly) — hand verdicts (machine checks in §3.3 of this report)

- **Theorem 7.8 (Theorem F)**, step by step:
  1. *The walk* — `d_1` integer, non-increasing, jumps only at the boundary `b'` of `J'` (type 1) or at its mirror
     (type 0): HOLDS. The real fit `fit(x_{H'}) + d_1`: HOLDS (real part of 7.2(b)). «the integer fit of
     `x_{H'} + d_1` is `X_1 = ŷ' + d_1`»: **rests on the integer part of Lemma 7.2(b), which is false in general**
     (see §7.1–§7.3 above). It is correct iff no level set of `fit(x_{H'})` of non-integer value straddles the jump
     of `d_1`. The text does not prove this. → GAP (or ERROR if it fails in some house — machine test below).
  2. *(Λ)*: `d_1 ≤ α2^c − h + κ ≤ α2^c` since `κ_t ≤ h_t`; HOLDS given step 1.
  3. *(Cut)*, cases (a)–(d): HOLDS given step 1 (I re-derived `J_H = (J', 1)`, `(0, J')`, `0`; the positivity
     `X_1 ≥ α` before `b` uses (Λ) for `H'` and passes to the real fit because a level-set mean lies between the
     floor and ceiling values; case (c) the second half `x_{H'} + d_2` with `d_2` as printed, `X_2(b') ≤ −α`).
  4. *Inherited potential* `v' = R_H + φ`: HOLDS — slack `h` on same-half arrows from `γ_I = γ_{I'} + h`, slack 0
     when `c ∈ a∖b`; (E) for `v'` with `X_1`; (M) inside halves.
  5. *Junction* `v'({c}) − v'(I') = −X_1(I') ≤ h − α`: HOLDS (uses `V'(∅) − V'(I') = ŷ'(∅) = −ŷ'(I')`).
  6. *No central flat*: HOLDS (needs `X_1` non-increasing — Lemma 7.9).
  7. *Central flat*: HOLDS — the interval `[max(c_3, v'(p^*)), min(c_4, v'(p))]` is non-empty because
     `c_3 ≤ c_4`, `c_3 ≤ v'(p)`, `v'(p^*) ≤ c_4`, `v'(p^*) < v'(p)`; its ends are integers.
  8. *Checks*: HOLDS — I redid all six cases of (G) with an end in `F`, plus the impossible ones (`a ∈ F_1`,
     `b ∈ F_2` cannot happen since `b` precedes `a`), and (M) across `p`, `p^*`.
  Verdict on Theorem F: **HOLDS modulo step 1** (the integer-shift claim), which is a GAP of the proof as written.
  **Repair (mine), machine-supported:** strengthen (Cut) to *strict* (Cut): «if `J_H ≢ 0` and its boundary `b > 0`,
  then `fit(x_H)_{b−1} > fit(x_H)_b`». The same induction proves it: in case (a) `Z_1(b−1) − Z_1(b) ≥ h ≥ 1` because
  `d_1` drops by `h` at `b` and `fit(x_{H'})` is non-increasing, and `Z_1(b−1) > 0`; in case (b) `fit = max(Z_1,0) > 0`
  at `I'` and `≤ 0` at `{c}`; in case (c) `d_2` drops by `κ = h ≥ 1` at `b'∪{c}` and `Z_2 < 0` from there (if
  `b' = ∅` the left neighbour is `I'`, where the fit is `≥ 0`). The mirror follows by antisymmetry. Since `d_1`
  (resp. the penalty shift, resp. the deletion at `{t_1}`) jumps only at the boundary of `J'` (resp. `J_H`) or
  its mirror, where `κ ≥ 1` makes the jump non-trivial, a strict cut there means no level set is split, and the
  integer claim of 7.2(b) becomes true in every application. Machine: `engines/theoremF_check.py`,
  `logs/theoremF_k7.log` — all 43 690 houses with `k ≤ 7`, `α ∈ {1,2}`: 0 straddles of any value at the 20 052
  jumps of `d_1`, at every cut `b` and its mirror, for the penalty shifts `P ≤ 6` and the deletion; the literal
  construction of `V` satisfies (E), (M), (G) everywhere; (Cut), (Λ), Lemma 7.9 and the step-1 formula hold
  everywhere. Controls (c_F one below the interval; skipping the central-flat fix) are detected in 2 550 and 2 808
  of the 3 979 houses with a central flat.
  The «plain reading» paragraph after the proof is accurate.
- **Lemma 7.9 (integer separation; every integer fit is non-increasing).** The induction «level sets of the first
  half are those of `fit(x_{H'})` shifted by `d_1`» has the same hidden assumption (no straddling at a jump of
  `d_1`). Note: integer separation alone does not exclude straddling — if a straddling level set of non-integer
  value `μ` is split by an integer jump `δ_1 > δ_2`, the two pieces still satisfy `⌊μ+δ_1⌋ ≥ ⌈μ+δ_2⌉`. Verdict:
  **GAP (same root)**; the conclusion is tested by machine (my S7: no violation in 22 650 cells).
- **Theorem 7.10.** `i ≥ 1`: (U1), (U3) HOLD (`v − w` terms cancel the penalties exactly; loops give 0). (U2) «is
  the integer fit of the clocks of the cell by (Cut) and Lemma 7.2(b)» — **same GAP**: the penalty shift
  `−P_rJ_H(D) + P_cJ_H(I∖D)` jumps at the boundary `b` of `J_H` and at its mirror. `i = 0`: the zero row gives `∞`
  and the `(N−1)×N` matrix `M^♯`; costs of the house `H^♯ = (I, k, K−1, α)` with `J_{H^♯} = [D ≠ ∅]` — HOLDS;
  «by (Cut) at `{t_1}`, the integer fit of `x^♯` restricted to `D ≠ ∅` is `ŷ_{H^♯}` restricted» — **same GAP**
  (if the level set of `∅` reached `{t_1}` with non-integer value, deleting `∅` would change the rounding); the
  adaptation of Lemma 6.1, Theorem O, Corollary 6.3, Lemma 6.4 and Theorem 7.4 to the `(N−1)×N` matrix is
  correct (for `r ≤ N−1`, `L_r ∌ ∅`, `F_r ∌ I`), but «with the same proofs» is terse for a non-square matrix.
- **§8 Proof of the Main Theorem.** Uses exactly: Theorem 3.8, Lemma 3.7, Theorem D, Theorem 7.10, Proposition 5.3,
  Proposition 5.4, Proposition 5.2 (for `I = ∅`), Lemma 7.9 — all proved earlier; nothing unproved is invoked
  except through the GAP above. The `I = ∅` case: `u_i(∅) = φ(K) + κ(i−1, K) = k + K + κ(m,K)` — HOLDS. The `i = 0`
  case matches the convention «∞ first, not pooled». Mission question 4 («does it use every piece it names, and
  nothing it has not proved?»): **yes, modulo the integer-shift step**. PRESENTATION: Theorem O, U and F are not
  named in §8 (they enter through 7.10) — fine.

#### §9 Consequences (read hardest) — against Gao et al. in their own notation

- **Lemma 9.1** (every raw clock with `(i,D) ≠ (0,∅)`, and every pooled big clock, is `≥ 2`). · **HOLDS** (`ξ = 1`
  forces `D = I = [0,k)`, then `h(D) = k ≥ 1`).
- **Proof of Corollary 1.5** (Bai's counts). · **HOLDS**: `(2^n − 2m_1(n) − 4m_2(n))/4` with Lemma 3.7 gives
  `2^{n−2} − 2^{(n−3)/2}` (odd n) and `2^{n−2} − 2^{(n−2)/2}` (even n) `= a_n`; the families `λ = 1, 2` are the
  only ones without small clocks.
- **Lemma 9.2** (a) `φ(λ+1) + τ(P_l) = φ(Y_l)`; (b) the max of `φ` on `[1, N]` is attained at a clearing of `N`;
  (c) the `Y_l` are the clearings of `λ+1`. · **HOLDS** (b: `y ≤ N_q`, `v_2(N_q) ≥ q`). Same content as
  [GMMY24, Remark 4.4] («successively changing the last nonzero digit to zero») — the paper could cite it.
- **Proposition 9.3 (shift 1).** · **HOLDS** (house `(I,k,0,1)`: no carry, `J ≡ 0`, `R_0 = R_K = τ`; step 1 of
  Thm 7.8 becomes a Lindley recursion `y_j = max(y_{j−1} − τ_{t_j}, 0)`; `k + K = φ(λ+1) + τ(I)`). Inherits the
  integer-shift GAP of step 1 (repaired in §7 above).
- **Proposition 9.4 (shift 0).** · **HOLDS** (house `H^♯`: all windows of type 1 and saturated, `τ_t = −2^t`,
  `J' = [D_0 ≠ ∅]`, `d_1 = 2^{t_j} − h_{t_j}[D_0 ≠ ∅]`, `ŷ_1({t_1}) = −2^{t_1}`). PRESENTATION: inside this proof
  `τ` denotes two different things in one sentence («`τ_t = −2^t` in the notation of §7.3» and «`−τ_{t_j}` with
  `τ` as in this subsection»), which is confusing.
- **Proposition 9.5 (the ceiling)** big clocks at shift `i ≥ 1` are `≤ g(n−i+1)`. · **HOLDS.** (H) the head is
  dyadic — needs that the penalty shift does not split the head (strict cut, see §7); (M) the reduction
  `κ(m, Y_l + o_D) − κ(m, o_D) = κ(m_h + c_D, Y_l/2^q)` — I re-derived it; (K) **Lemma K** — re-derived: carries
  of `a + B` are born only at bits `≥ v_2(B)`, so `κ ≤ p − v_2(B)`, and `y = 2^q((a+B) − ((a+B) mod 2^p))` gives
  `y ≥ 2^q(B+1)`, `v_2(y) ≥ q + p`; the final bound `Y_l + 2^q(m_h + c_D) ≤ λ + 1 + m = n − i` — correct.
  PRESENTATION: Lemma K is a free-standing lemma stated inside a proof; it deserves a number.
- **Lemma 9.6** (`m_{n−2}(n) = n − 1 − [n even]`; `m_{n−4}(n)` for odd `n`). · **HOLDS** (weight peeling; I checked
  `m_3(7) = 14`, `m_1(5) = 4` against my recursion).
- **Proof of Corollary 1.6.** · **HOLDS**, every case re-derived (steps 1–4 and the particular cases, `n = 3` by
  hand). One counting slip, PRESENTATION: step 3 says the even case gives «`2(n−2) ≥ n` factors» at `G`; when
  `c_1 = G` (i.e. `φ(n) − 1 ≤ G`) one needs `n + 1` of them. It is fine — `2(n−2) ≥ n+1` for `n ≥ 6`, and for
  `n = 4`, `c_1 = φ(4) − 1 = 5 > G = 3` — but the text should say so.
- **Lemma 9.7, Lemma 9.8, Theorem 9.9 (the mirror that doubles), proof of Corollary 1.7.** · **HOLDS** (I redid
  `φ(ξ) = 2^e − 2J + 1 + v_2(J)`, `κ(J−1, ξ) = s_2(J) − 1`, `κ(J'−1, ξ') = s_2(J'−1)`, `v_2(i) = t_1 − 1`, and
  that a doubled sequence has the doubled fit and the same integer multiset). Machine: Corollary 1.7 for `e ≤ 8`
  from the rule (§3.1b) and directly from the Smith form for `n = 2, 4, 8`.

**Against the sources** (`material/sources/GaoMarxKuoMcDonaldYuen_arXiv1912.06919v3.txt`, poster `.txt`):
- [GMMY24, Theorem 4.1] (txt line 890): `v_2(c_1(Q_n)) = max(max_{x<n}{v_2(x)+x}, v_2(n)+n−1)` for `n ≥ 2` — the
  paper's `c_1 = max(g(n), v_2 n + n − 1)` is the same statement (`g(n) = max_{1≤x<n} φ(x)`). The paper recovers
  it for `n ≥ 3` (the case `n = 2`, `K(Q_2) = Z/4`, is trivial) — correct and not over-claimed.
- [GMMY24, Theorem 4.2] (line 895): `c_2 = ⋯ = c_{n−1} = max_{x<n}{v_2(x)+x}`, `n ≥ 3` — same.
- [GMMY24, Conjecture 4.14] (line 1156): `v_2(c_n(Q_n)) = max(max_{x<n−1}{v_2(x)+x}, v_2(n−1)+n−3)`, `n ≥ 3` —
  **exactly** the paper's `c_n = max(g(n−1), v_2(n−1) + n − 3)`. GMMY's `c_i` is «the size of the i-th largest
  cyclic factor of K(Q_n)» and they take `v_2`; the paper's `c_i` are the exponents of `Syl_2`. Same thing,
  since the `i`-th largest invariant factor has `v_2` equal to the `i`-th largest exponent. A one-line remark on
  this change of notation would help.
- Poster [GMM19] (txt lines 11–14): «for n ≥ 4 that c_{n+1}(Q_n) = max_{x<n−1}{v2(x) + x}», with `c_k(G)` defined
  on the poster as the exponent of the `k`-th largest cyclic factor of `Syl_2(K(G))` — **exactly** the paper's
  `c_{n+1} = g(n−1)`, `n ≥ 4`.
- [GMMY24, Conjecture 5.4] (line 1179): `Syl_2(K(Q_{2^k})) ≅ Syl_2(K(Q_{2^k−1}))^2 × Z/(2^{2^k+k−1}Z)` —
  **exactly** Corollary 1.7 with `e = k` (the paper renames `k` to `e` because `k` is taken; fine).
- [GMMY24, Table 1] (lines ~1196–1210, «table from [2]», i.e. from Bai): `Syl_2 K(Q_n)` for `n ≤ 11`. **My Smith
  forms agree with this table entry by entry for n = 7..11** (I compared all five rows) — a third, independent
  confirmation of the rule for `n ≤ 11`. The paper does not mention that this table exists; it could.
**Verdict §9: HOLDS; the corollaries say exactly what Gao et al. conjectured, in their notation.**

#### §10.1–§10.3 The fold on the families, the half-size lattice, the formal dance

- **Lemma 10.1** (`a = x_1⋯x_n` acts as `(−1)^{(n−H)/2} exp(F)`; on `T(λ)` at shift `i`, `(−1)^{D+i} exp F`).
  · **HOLDS** (`x = 1 − s`: `b_0 ↦ b_0 − b_1`, `b_1 ↦ −b_1`; `exp F` and `(−1)^{floor}` are group-like).
- **Corollary 10.2**, **Proposition 10.3** (fold law reduces to `X̄(λ,i) ≅ 2X(λ,i)` family by family). · **HOLDS**
  (`2(Z/2^{e+1}) ≅ Z/2^e`, `2Z_2 ≅ Z_2`; torsion of a f.g. `Z_2`-module is determined).
- **§10.2 power series.** `Ch = cosh u`, `Sh = sinh(u)/u` with `u^2 = 2F`; `(Ch−1)/Sh = u tanh(u/2)`,
  `(Ch+1)/Sh = u coth(u/2)`; `η_m = 2(2^{2m}−1)B_{2m}/(2m−1)!!`, `η'_m = 2B_{2m}/(2m−1)!!`. · **HOLDS** — I re-derived
  both expansions from `tanh x = Σ 2^{2m}(2^{2m}−1)B_{2m}x^{2m−1}/(2m)!` and `x coth x = Σ 2^{2m}B_{2m}x^{2m}/(2m)!`,
  with `u^{2m}/(2m)! = F^{(m)}/(2m−1)!!`; `η_1 = 1`, `η'_1 = 1/3`. · External: **von Staudt–Clausen**
  (`p = 2` always divides the denominator of `B_{2m}` exactly once, so `v_2(B_{2m}) = −1`) — correct use; all
  `η_m`, `η'_m` are 2-adic units.
- **Lemma 10.4 (odd families)** (a) `X̄(λ, j) ≅ coker Ψ_j`; (b) `2X(λ, j) ≅ coker Σ_c`. · **HOLDS.** (a): `a(b_0n) =
  ε[b_0Ch(n) − b_1Sh(n)]`, `{b_0n, ab_0n}` a basis (Sh invertible), circulant `[[P,Q],[Q,P]]`, coinvariants give
  `P + Q = Ψ_j`. (b): `π'(f) = −2(j+2f)(j+2f+1) = −4(c+f)u_f`, `2·coker(2G') = coker G'`, then right
  multiplication by `(−u(D))^{−1}` and conjugation by `s(D)` with `s(f+1) = −u_f^{−1}s(f)` give `Σ_c` — I checked
  the conjugation floor by floor.
- **`glue`** and **Lemma 10.5 (even families)**. · **HOLDS** (`F_V + 2D_V = 1 − g`; modulo `a − 1`, `g ≡ a_M`;
  modulo `τ_i`, `g ≡ 1 + τ_M` and `g^2 = 1` give `coker τ_M(τ_M+2)`; `τ_M(τ_M+2)/2 = F^{(2)} + 2F(J+1) + 2J(J+1)`
  using `JF = F(J+1)`; `θ = f·h`; the row/column operations turn a circulant into `glue(w_−, w_+)`; `w ↦ w_±` are
  ring maps with `τ_M ↦ Ψ_i` and `τ_M ↦ Ψ_{i+1} − 2`). The remark `Ψ_{i+1} − Ψ_i = 2(1 + εSh^{−1})` — HOLDS.
- **§10.3 formal operators `𝔅`, doblar map, `V`-split, moves.** · **HOLDS** (I re-derived the product rule from
  `F^{(a)}φ(D) = φ(D−a)F^{(a)}` with coefficients at the target floor; the four blocks `x^{ee'}` from 3.1(b) with
  the target floors `2(f+q)+e`; the `V`-split `[[x,0],[x',x^+]]`). · PRESENTATION (minor): the values `x_m(g)` for
  `g < m` never act (no vector of floor `g−m < 0`), so `𝔅` is really a quotient; «multiplicative since this is
  the action on `Φ(N')` for every `N'`» silently uses that `𝔅` acts faithfully on large Weyl lattices modulo
  those values. Harmless.
- **Lemma 10.6** (the formal moves reproduce Propositions 4.1–4.2; `M_w(σ^{(α)}_c) = M^{(α)}(l, c)`). · **HOLDS**
  — the change of basis `B_n = b_0⊗b_1n − C_n` adds a pivot column to a non-pivot column and a pivot row to a
  non-pivot row, which leaves the Schur complement unchanged (`S' = D + BX − BP^{−1}(C + PX) = S`).
- **Proposition 10.7** (clean dance ⇒ small clocks ⊕ `coker(2^k M_w(G))`). · **HOLDS** (as Prop. 4.3).

#### §10.4–§10.8 Rigidity, cleanliness, odd and even families, assembly (read hardest)

- **Lemma 10.8 (inverse block)** `G_h^{−1} = 2^h ρ_h Ξ^{−1} κ_h`. · **HOLDS** (block-inverse identity: the
  (remaining sources × remaining coordinates) block of `G^{−1}` is `S^{−1}`; offsets: doblar / paso `v=0` add `0`
  and `2^h`, paso `v=1` adds `2^h` and `2^{h+1}` — I redid the induction). External: block-inverse (Schur)
  identity — correct use.
- **Corollary 10.9** (`(M_w(Ξ)^{−1})_{YX} = 2^kγ_{YX} y_L(o_Y+K−1)`). · **HOLDS** (only one `L` lands on the floor
  read by `ρ`).
- **Lemma 10.10 (path sum)** `y^Ξ_L = y^Σ_L(1 + ε_L)`, `v_2(ε_L) ≥ α − 1`. · **HOLDS** (Neumann series; each
  composition skips `Σ(m_i−1)` floors, each worth `≥ α`, against `v_2(m_i!) ≤ m_i − 1`).
- **Factorization** `M_w(Σ) = 𝔡_1𝒜𝔡_2`. · **HOLDS** (I multiplied it out: `(2η)^{o_D−o_{D'}}η^{1−K}` reproduces
  `η·η^{−(K−o(Δ))}2^{o(Δ)}`).
- **Lemma 10.11 (stability).** · **HOLDS** (Hadamard product commutes with diagonal scalings; `𝒜^{−1}` = multiplication
  by `q_k^{−1}`, entries `≥ δ` by subadditivity; the chain bound `≥ δ(D∖D') + j`).
- **Theorem 10.12 (rigidity).** · **HOLDS.** The key sentence «the Smith form … is computed from the valuations of
  its entries and from its support alone» is correct: Lemma 6.1, Corollary 6.3 (unique golden term), Lemma 6.4 and
  Theorem 7.4 use only costs and support. (It inherits the §7 GAP only through Theorem 7.10, repaired above.)
  The conjugation `η^{−D}(ηF + π)η^D = F + π` — checked floor by floor.
- **Lemma 10.13 (the ring 𝒦, the shadow ring 𝒮, Θ).** · **HOLDS.** (a) uniqueness by **Strassmann** (the series
  `(a−a') + 2(χ−χ')(2Y)` is restricted and has infinitely many zeros) — correct use; ring, shifts
  (`χ(X−2e) = χ(−2e) + χ̃(X)`, `χ(−2e) ∈ 2Z_2`), inverses. (b) `Θ` multiplicative because `ε^2 = 0`; shift-invariant
  because `Σ_{n≥j}c_nC(n,j)(−2e)^{n−j} ≡ c_j` and `2χ(−2e) ∈ 4Z_2`; `ker Θ = 2𝒦`. (c) `φ ≡ a (mod 4)`.
- **Lemma 10.14** (`𝒯_h` is a ring; `Θ_h` a ring homomorphism to the commutative `R_𝒮`; `β^2 = β_0^2`). · **HOLDS**
  (product formula with the shift `a2^h + o(Δ_1)` re-derived; `C(2q, q)` even for `q ≥ 1`, `E_t^2 = 0`).
- **Theorem 10.15 (cleanliness).** · **HOLDS.** Doblar: the four blocks have the printed coefficient functions at
  positions `y'` / `y' + 2^h`; `P` is a unit plus a nilpotent (raises `m` or `Δ`), so `P^{−1} ∈ 𝒯_{h+1}`;
  `Θ(Dd) = 0` (factor `2q+2`), `Θ(B) = Θ(C)`, `Θ(S) = −β^2Θ(P)^{−1} = −(εχ̄)^2Θ(P)^{−1} = 0`; new payment
  `≡ 0 (mod 8)`, new `F`-coefficient `Γ_{∅,1}(y') − 2(…)` odd. Paso: the `V`-split keeps `Γ_{Δ,m}` on the diagonal
  blocks and creates `Γ^{new}_{Δ∪{h},m−1} = Γ_{Δ,m}` — well defined and covariant (positions
  `2^h(g+1) + o_D + c = 2^hg + o_{D∪{h}} + c`). Level 0: `2^αy = 2χ(2y)` with `χ = 2^{α−2}X`, in `𝒦` iff `α ≥ 2`.
  **Mission question: the induction is well founded** — it is a finite induction on the level `h = 0, …, k`, each
  step proving membership in `𝒯_{h+1}` and (a), (b) for the next system. **Every hypothesis of Theorem 10.12 is
  established by Theorem 10.15** for the operators where 10.12 is used (`Ψ_j`, `Σ_c`: `α = 2`, constants
  `ζ_m = η_m` or `η'_m`, units `η = 1` or `1/3`, `c = ⌈j/2⌉ ≥ 1`); Lemma 10.8's two hypotheses (invertible over Q,
  pivots invertible) follow from `c ≥ 1` and cleanliness.
  Remark (2) (failure of cleanliness with generic payments or floor-dependent units) is a numerical claim — tested
  in §3.4 of this report.
- **Theorem 10.16 (odd-family operators) and the continuity at `c = 0`.** · **HOLDS.** For `c = 2^n → 0` in `Z_2`,
  rigidity gives `v_2(M_w(Ξ_c) − M_w(Σ'_c)) ≥ v_2(M_w(Σ'_c)) + 1` entrywise; entries are continuous in `c` (finite
  composition of ring operations, odd denominators, inversion of unit-diagonal pivots, exact halving); a closed
  ball argument passes the inequality to the limit; zero entries of `M_w(Σ'_0)` force zero entries of `M_w(Ξ_0)`.
  Same support ⇒ row `∅` of `M_w(Ξ_0)` vanishes, and Theorem 7.10 at shift 0 uses only support and valuations.
  **Mission question: the continuity step at `i = 0` is correct.**
- **Corollary 10.17 (fold law, odd families).** · **HOLDS.**
- **Lemma 10.18 (modulo 2).** · **HOLDS.** Note: the hypothesis «`G ≡ G' (mod 2)` at every position» only controls
  `𝔞` modulo 2, not `Θ`; the proof correctly uses only `𝔞` modulo 4 (values `≡ 𝔞 (mod 4)`), and the decisive step
  `β^2 ≡ β_0^2 ≡ 0 (mod 2)` holds because payments are `≡ 0 (mod 4)`. I checked each of the three changes
  (`𝔞(Dd)` by `4·`, `β^2` by `4βδ' + 4δ'^2`, `β^2π^{−1}` by `−2β^2π^{−2}δ''`).
- **Lemma 10.19 (the glue).** · **HOLDS** (conjugation by the scalar `L` on the outer slot commutes with every
  move; `glue(U, U')` integral iff `U ≡ U' (mod 2)`; its Schur complement `≡ 0 (mod 2)` iff `S_U ≡ S_{U'} (mod 4)`).
- **Lemma 10.20 (the bend)** `M_w(Ψ)N_± ∈ 2·Mat(Z_2)`. · **HOLDS** (`v_2(π/(π±2)) = w(d)`, skipped floors worth
  `w(d)+1` against `v_2(m_i!)`; `v_2((𝔡_1)_D) = 1 − K − W[0, o_D−1]`; the telescoped window `[o_D, o_Y+K−1]` is
  non-empty because `o_{D∖Y} ≤ K − 1`, and `w ≥ 1` on it).
- **Corollary 10.21.** · **HOLDS** (`Θ(Ψ)^2 = (εX)^2 = 0`; payment `4y(2y±1) = 2χ(2y)`, `χ = X^2 ± X`; `F`-coefficient
  `η(4y − 2 ± 1)`; partial fractions; `W_+ = (I − M_w(Ψ)N_+)^{−1}`, `W_− = −(I − M_w(Ψ)N_−)^{−1}`).
- **Theorem 10.22 (fold law, even families).** · **HOLDS.** I re-derived `U − U' = ΨY_0 + Y_0Ψ − 2Ψ + 2Y_0^2 − 2Y_0
  ≡ [Ψ, Y_0] = 4[D, Y_0] ≡ 0 (mod 2)` (the parenthetical warning that `Ψ_i` and `Y_0` do not commute is right and
  important); for `i ≥ 1` the final matrices differ by `glue(W_−, W_+) ∈ GL(Z_2)` (`(W_+ − W_−)/2` integral);
  for `i = 0` the parameter `c ∈ Z_2` with `c = 2^n → 0`, continuity of `M_w(·)` and `N_±` (denominators
  `4(d+c) ± 2` never vanish), closedness of `2·Mat`. Correct.
- **§10.8 Proof of Theorem DW; Corollary 1.4; the mod-2 layer.** · **HOLDS.** The odd part of Corollary 1.4 uses
  the folded-cube eigenvalues `2|J|`, `|J|` even (characters trivial on `𝟙`) — standard, stated in §1.3 but not
  derived; fine. The mod-2 layer is exactly [GMMY24, Proposition 2.12] (`M_r` = unit vectors + all-ones of
  `F_2^r`, i.e. the folded `(r+1)`-cube) — the paper says so. Machine: F_2-rank `= a_n` for `n ≤ 12` (§3.1).
- **Remark «what the fold sees».** Heuristic, honest; the `x_1x_2` claim is backed by my control c3 (§3.1).
**Verdict §10: HOLDS** (every step re-derived; no gap found in §10 itself).

## 3. The numbers, with my own code (with controls)

### 3.1 The rule against the graph (written from §1 alone, before reading §2) — DONE 2026-10-05

Engines: `engines/rule.py` (the rule of §1.2 transcribed literally: multiplicities by the `V·` recursion, raw clocks
`u_i(D)`, PAVA with strictly decreasing block means, the integer rounding, small clocks), `engines/smith2.py` (my
own exact 2-adic Smith form: elimination modulo `2^32` in numpy unsigned integers, pivot = any odd entry, divide by
2 when none is left; no floats), `engines/check31.py` (driver). Engine controls (`engines/test_smith2.py`,
`logs/test_smith2.log`): 80 random unimodular scrambles of known diagonals (E = 32 and 64) recovered exactly, each
with a deliberately wrong expectation that is rejected; agreement with sympy's `smith_normal_form` on 13 small
Laplacians; E = 32 = E = 64 on Q_1..Q_9. All PASS.

| check | n | result | log |
|---|---|---|---|
| A. rule of §1.2 == Syl_2 of `L(Q_n)` (with one free summand) | 1..12 | **PASS for every n** | `logs/check31_1_9.log`, `logs/check31_10_11.log`, `logs/check31_12.log` |
| B. exactly one free summand; Σ exponents = v_2(τ(Q_n)) and v_2(τ(folded)) from the eigenvalue product | 1..12 | PASS | same |
| C. Theorem DW: Syl_2 of the folded Laplacian == 2·Syl_2 K(Q_n) | 1..12 | **PASS for every n** | same |
| D. "equivalently" form with `a_n = 2^{n−2} − 2^{⌊(n−2)/2⌋}` | 2..12 | PASS | same |
| control c1: rule with the lowest digit of `I` dropped | 2..12 | **fails** (as it must) at n = 2, 4..12 (n = 3 has no family with I ≠ ∅) | same |
| control c2: `a_n ± 1` in the form D | 2..12 | **fails** at every n | same |
| control c3: `Q_n/⟨x_1x_2⟩` in place of the folded cube | 2..12 | **fails** at every n ≥ 3 (at n = 2 both are `Z/2`) | same |

Verdict 3.1: **HOLDS numerically for n ≤ 12**, and the answer to mission §2.5 is **yes: a reader with only §1 can
compute Syl_2 K(Q_n)** — I did so for n = 7 (`{1: 28, 2: 1, 4: 8, 5: 6, 6: 14, 7: 6}`) and every n ≤ 12 from §1
alone, with no ambiguity I had to resolve by guessing. The only point that needs care is the phrase «block means
strictly decreasing»: PAVA must merge equal adjacent means too, otherwise the integer rounding differs (e.g. two
blocks of sum 7 and size 2 give 4,3,4,3 instead of 4,4,3,3). The paper says «strictly», so it is specified; a
sentence warning the reader would help (PRESENTATION, §1.2 «Pooling»).

The §1.2 example (n = 6) and the §1.3 example (n = 5 folded, `{2: 4, 3: 1, 5: 4}`) are reproduced by the Smith
form exactly.

n = 12 values (Smith form = rule): `Syl_2 K(Q_12) = {1: 992, 2: 132, 3: 64, 4: 200, 5: 164, 6: 1, 8: 164, 9: 201,
11: 128, 13: 1}`, `Syl_2 K̄(12) = {1: 132, 2: 64, 3: 200, 4: 164, 5: 1, 7: 164, 8: 201, 10: 128, 12: 1}`
(time 23 s + 3 s, peak 475 MB).


### 3.1b Internal checks of the rule and the numbers of §1.4 (from the rule; no Smith form)

`engines/check_rule_internal.py`, `logs/rule_internal_300_100_300.log` (after one run killed by the vigía for my
own bug, see §8):
- the «equivalent form» of §1.2 (Proposition 5.3): `u_i(D) = k + K + κ(m, K) + x_D` for all 363 600 triples with
  λ ≤ 300, 1 ≤ i ≤ 100 — **0 mismatches**;
- the integer antitonic fit is non-increasing (the claim of §1.2 citing Lemma 7.9) for all 22 650 pairs with
  λ + 2i ≤ 300 — 0 violations; pooling acts in 8 521 of them;
- the «strictly decreasing» clause never matters there (merging equal means or not gives the same integers in all
  22 650 cases) — so the subtlety I flagged in 3.1 is moot on the data, but the definition is still the right one;
- no big clock is 0 (so no trivial factor hides inside Corollary 1.5's count), λ + 2i ≤ 300;
- **Corollary 1.5** for n = 2..300, **Corollary 1.6** (three cases) for n = 4..300 and its «in particular» forms
  for n = 3..300, **Corollary 1.7** for e = 1..8: **0 failures** as consequences of the rule. Controls: Cor 1.5
  with the floor `⌊(n−1)/2⌋` instead of `⌊(n−2)/2⌋` fails at 149 values of n; Cor 1.6 with `φ(n−1) − 1` instead
  of `− 2` fails at 65 values. Since the rule equals the Smith form only for n ≤ 12 by my computation, for
  n > 12 this checks the derivation of the corollaries from the Main Theorem, not the theorem.
- «This is the smallest cube in which pooling acts» (§1.2): checked n = 4, 5 by hand and by `logs/example_n6.log` —
  HOLDS.

### 3.2 Every number printed in §1 and §9 that I could recompute

| where | printed | mine | verdict |
|---|---|---|---|
| §1.1 | `τ(Q_n) = 2^{2^n−n−1}∏ j^{C(n,j)}` | 2-part = Σ of my Smith exponents (n ≤ 12); odd part = Bai's (my p-adic Smith, p = 3,5,7, n ≤ 9) | HOLDS |
| §1.2 | `n = 6`: `m = 1, 4, 4`; raw clocks `∞,6,6,3`; `5,7 → 6,6`; `5,2`; `{1:12, 2:4, 3:1, 5:4, 6:10}` | identical (`logs/example_n6.log`, Smith form) | HOLDS |
| §1.2 | «smallest cube in which pooling acts» | n = 4, 5 checked: no pooling | HOLDS |
| §1.2 | «`n = 1024` takes seconds» | 0.2 s after warming my multiplicity cache; `2^{1023} − 1` factors; top exponent `1033 = 2^{10}+10−1` (Cor. 1.7) (`logs/time1024.log`) | HOLDS |
| §1.3 | `Syl_2 K(Q_5) = {1:6, 3:4, 4:1, 6:4}`, `a_5 = 6`, `Syl_2 K̄(5) = {2:4, 3:1, 5:4}` | identical (Smith form of both Laplacians) | HOLDS |
| §1.3 | F_2-rank of the folded Laplacian `= a_n` | valuation-0 count of my Smith forms, n ≤ 12 | HOLDS |
| §1.3 | `Q_n/⟨x_1x_2⟩` does not halve the group | fails for every `n = 3..12` (`n = 2` coincides) | HOLDS |
| Cor. 1.4 odd part | `Syl_p K̄(n) ≅ Syl_p ⊕_{j even}(Z/2j)^{C(n,j)}` | p = 3,5,7, n = 2..11: 30/30 (`logs/check_part3.log`) | HOLDS |
| Cor. 1.5–1.7 | formulas | from the rule n ≤ 300 (1.5, 1.6), e ≤ 10 (1.7); directly n ≤ 12 | HOLDS |
| §9.2 | `Syl_2 K(Q_3) = {1:1, 3:2}` | identical | HOLDS |
| Lemma 9.6 | `m_{n−4}(5) = 4`, `m_3(7) = 14` | identical (my recursion) | HOLDS |
| §9.3 | `u = 2^e + e − 1` for the dancer `{0}` of the family `2^e` | rule; Smith n = 2, 4, 8 | HOLDS |
| §11 Q2 | turned lid: `Syl_2 K(Q_a□C_b) ≅ Syl_2 K(Q_b□C_a)`, `n ≤ 12`; `2·Syl_2K(Q_n)` only for `b = n` | confirmed for every `n = 3..12` (`logs/check_part3.log`) | HOLDS (as a measurement) |
| §1.3 | OEIS A193134 = number of spanning trees of the folded cube, `n ≥ 3` | see §4 (web) | — |

### 3.3 One proof by machine (mission §3.3): the floor of §7, and the whole chain §3–§7 cell by cell

The step I trusted least is **Theorem F (§7.4) together with its use of Lemma 7.2(b)** (the integer part of 7.2(b)
is false as stated; see §2). I gated it at three levels, each with a control that can fail and does:

| gate | what it checks | range | result | control | log |
|---|---|---|---|---|---|
| `engines/theoremF_check.py` | literal construction of `V` (steps 1–8 of the proof), (E) against the TRUE integer fit, (M), (G) on all arrows; (Cut); (Λ); Lemma 7.9; step-1 formula; integer-shift claims of step 1, Thm 7.10 (U2) and the `i = 0` deletion; **straddle detector** | all 43 690 houses `k ≤ 7`, `α ∈ {1,2}`, penalties `P ≤ 6` | **0 failures; 0 straddles of any value** at the 20 052 jumps of `d_1`, at every cut and its mirror | `c_F − 1` detected in 2 550/3 979 flat houses; «no flat fix» in 2 808/3 979 | `logs/theoremF_k7.log` |
| `engines/cells_smith.py` | `M^{(α)}(λ,i)` from the closed form of Thm 4.4; deficit law; `v_2` of every support entry = cost form (5.2/5.4); exact Smith form of `M` = Thm 7.10 prediction | 7 874 cells: `λ ≤ 127`, `0 ≤ i ≤ 30`, `α ∈ {1,2}` | **0 failures** (338 582 entries, 1 093 coefficients) | raw clocks rejected in all 1 876 pooling cells | `logs/cells_smith_127_30.log` |
| `engines/family_lattice.py` | `T(λ)` built from §3 definitions; exact Smith form of `σ^{(α)}_i` on it = Thm D + Thm 7.10 (and = `rule.X` for α = 1) | 1 401 cells: `λ ≤ 31, i ≤ 10` and `λ ≤ 63, i ≤ 8`, `α ∈ {1,2}`; 415 cells skipped (exponent ≥ 60), counted | **0 failures** | raw clocks rejected in all 274 pooling cells | `logs/family_lattice_*.log` |
| `engines/theoremO_brute.py` | number of golden bijections `L_r → F_r`; bit description = (γ = 0) | all `s ≤ 5`, `0 ≤ r ≤ 2^s` (69 pairs); 5 461 arrows (`k ≤ 6`) | **exactly 1** in all 69 pairs; 0 disagreements | «any run» / «any subset» golden give ≠ 1 in 26 / 42 pairs | `logs/theoremO_brute.log` |

Reading: the family groups `X^{(α)}(λ, i)` equal the printed formula for `α = 1` **and `α = 2`** far beyond the cube
range `n ≤ 12` (which only reaches `λ ≤ 12`, `i ≤ 5`); the hidden hypothesis of Lemma 7.2(b) (no straddling) holds
in every house tested, consistently with the strict-(Cut) repair I propose in §2.

### 3.4 Machine checks of §10 (the fold), with controls

| gate | what it checks | range | result | control | log |
|---|---|---|---|---|---|
| `engines/fold_family.py` | **`X̄(λ,i) ≅ 2X(λ,i)` from the definition** `T(λ)/(τ_iT + (a−1)T)`, `a = (−1)^{D+i}exp F` with divided powers built from Prop. 3.1(b) + coproduct (self-checks `F^{(1)} = F`, `r!F^{(r)} = F^r`, `a^2 = 1`, `aτ = τa`) | 513 cells, `λ ≤ 63`, `i ≤ 8` (54 skipped, exponent ≥ 60, counted) | **513/513** | `a → −a` detected 513/513 | `logs/fold_family_63_8.log` |
| `engines/dance10.py` | formal dance of §10.3 as explicit block eliminations on `T(l)`: `Σ_c` gives exactly `M^{(2)}(l,c)` of Thm 4.4 (Lemma 10.6(b)); `Ψ_j` (built from `Ch`, `Sh`, not from the Bernoulli series) dances clean (Thm 10.15), final matrix with the support, entry valuations and Smith form of `M^{(2)}(l,⌈j/2⌉)` (Thm 10.12; Thm 10.16 at `c = 0` incl. zero row `∅`); Bernoulli expansion of §10.2 | `l ≤ 31`, `0 ≤ j ≤ 7` (256 dances) | **256/256 on every item** | see next row | `logs/dance10_31_7.log` |
| `engines/dance10_controls2/3/4.py` | the cleanliness test can fail: `α = 1` (pivot not invertible), a floor-parity `F^{(2)}` coefficient (Schur ≢ 0 mod 2); positive controls in the class of Thm 10.15 (random constant `ζ_m`, unit `3`) | `l ∈ {3,5,6,7,15,23,27,29,30,31,63}` | controls fail every time; positives clean every time | — | `logs/dance10_controls{2,3,4}.log` |
| same | **Remark (2) of §10.5 / §12.2**: «with generic payments `4q_d` … cleanliness fails first at `l = 63`; with floor-dependent odd units on `F`, at `l = 31`» | same `l`, 12–50 random choices each, 20-bit and 200-bit randomness | **NOT reproduced: every such dance is clean** | — | same |

Reading: the fold law holds family by family far beyond the cube range (my cube check reaches `λ ≤ 12`; this
reaches `λ ≤ 63`), and the internal mechanism of §10 (clean dance, rigidity, continuity at `c = 0`) behaves
exactly as proved. The only claim of §10 I could not confirm is Remark (2): under the natural reading
(`Ξ = 4q(D) + F + Σ_{m≥2}η_mF^{(m)}`, resp. `4(D+c) + u(D)F + Σ_{m≥2}η_mF^{(m)}`) the dances stay clean. Perhaps
flight 9 measured loss of covariance / of the class `𝒦` (the §12.2 row on Theorem 10.15 speaks of «covariance and
𝒦 at every level»), which is not the same as loss of cleanliness. **Verdict on Remark (2): ERROR or
over-statement in a remark** (not used anywhere in the proofs); it should be restated as what was measured, or
removed.

### 3.5 The table of §12.2 (mission §3.4)

- **Plausibility for a laptop.** Every range is plausible: my own engines did more in less (`Q_12` in 23 s; 43 690
  houses in 27 s; 7 874 Smith forms of `M` in 6 min). The largest claims (`n = 13` direct Smith by cold reader 1:
  an `8192 × 8192` matrix, ≈ 270–540 MB and a few minutes modulo `2^{32}`/`2^{64}`; houses `λ ≤ 255`, `α ≤ 4`) are
  feasible with care.
- **Rows without controls.** By the paper's own definition («Controls are deliberately wrong variants that must
  fail») 13 of the 26 rows have none («—»), including the first row (the Main Theorem against the direct Smith form),
  Theorem D, Theorem 4.4, Propositions 5.2–5.4, Theorem 7.10, Theorem 6.2, Corollary 1.7, the weights `η_m`,
  Lemma 10.1, Theorem 10.22. A reader cannot tell from the table whether those checks could fail. (My own versions
  of all of them have controls that fail, so the statements are fine; it is the table that is under-documented.)
- **Rows stated more strongly than a check of that kind can show.**
  1. «Theorem 10.15: covariance and `𝒦` at every level … `≈ 10^6` pairs, 0 failures». Membership in `𝒦` is a statement
     about power series on `Z_2`; a finite computation can only test necessary conditions (e.g. finitely many
     positions, finitely many digits, shift-invariance modulo 2). The row should say what was tested.
  2. The remark under the table: «with generic payments `4q_d`, cleanliness fails first at `l = 63`; with
     floor-dependent odd units on `F`, at `l = 31` (flight 9)» — **not reproduced** (§3.4 above): with my engine,
     which detects both failure modes, those dances are clean at every `l` tested up to 63. It is attributed to a
     «flight» the reader cannot see.
  3. «Theorem 7.8: … every claim of its proof» — fine as a check, but it did not detect (or the text did not
     record) that Lemma 7.2(b) as stated is false in general; a statement-level gate would have found it with
     random sequences. Minor.
  4. «Theorem 6.2: exactly one golden bijection — all `I` with `|I| ≤ 4`, every `r` — 61 cases». Theorem O depends
     only on `s = |I|`; the number of `(s, r)` pairs with `s ≤ 4` is 36, and I could not reconstruct «61». Harmless
     but unexplained.
     *(Added in Part 6, after opening the gates:* `gate_sections5to7.py` tests `s ≤ 3` only, plus six sets of size
     2–3 — exactly 61 cases. So the row's range «`|I| ≤ 4`» is overstated; see §6.)
  5. Theorem 10.22 «`i = 1, …, 6`»: the continuity case `i = 0` of the even families is not in that row (it is in
     the `X̄ ≅ 2X` rows with `i ≤ 5`/`i ≤ 6`). My `engines/fold_family.py` covers `i = 0` for all `λ ≤ 63`.
- Every row attributed to «cold reader 1/2» or «flight 9» refers to material that is not printed or cited in a
  retrievable way; as evidence it is unverifiable for a referee (see §5).

## 4. Sources, citations and priority

### 4.1 Quotations and «[X, n]» citations against `material/sources/` (txt line numbers; pages where printed)

| paper says | source | verdict |
|---|---|---|
| «The full structure of the Sylow-2 subgroup of the critical group of the n-cube is still unknown» [Bai03, p. 253] | `Bai_cube_group_LAA2003.txt` l. 144–145, on journal p. 253 | **exact** |
| Reiner conjectured in 2001 the two counts | Bai's ref. [17]: «V. Reiner, University of Minnesota Combinatorial Problem Session, 2001» (l. 610) | correct |
| `Syl_p K(Q_n) ≅ Syl_p ⊕(Z/j)^{C(n,j)}` [Bai03, Thm 1.2] | l. 96–103, p. 253 | correct |
| Cor. 1.5 = [Bai03, Thms 1.1, 1.3] | Thm 1.1: «K(Q_n) has exactly 2^{n−1} − 1 invariant factors» (whole group, l. 89); Thm 1.3: generating function and `a_n = 2^{n−2} − 2^{⌊(n−2)/2⌋}` (l. 133–143) | correct; PRESENTATION: Bai counts invariant factors of `K(Q_n)`, the paper counts cyclic factors of `Syl_2`; equivalent (odd Sylows have fewer factors), one sentence would say so |
| «the full structure of the 2-primary component of both the critical group and the Smith group of the n-cube remain unknown» [DJ14] | `DuceyJalil…txt` l. 308–309 (arXiv p. 7) | **exact** |
| «only the 2-Sylow subgroup of the critical group remains to be determined, for both odd and even n. We do not have any conjecture about its exact structure» [CSX17, §5.2] | `ChandlerSinXiang…txt` l. 852–854, §5.2 «Final remarks» | **exact** |
| monomial basis «[CSX17, §5, (5)]» | l. 183–185, eq. (5) in §5 «Bases for the free module on Q_n …» | correct (CSX's basis is `X_I` in `Z[X]/(X_i^2−X_i)`; «Laplacian analogue» is fair) |
| «the 2-Sylow subgroup of their critical groups, or even just the 2-rank of the Laplacians, has been rather difficult to understand» [IKKY22, §7] | `Adinkras_arXiv2202.02821.txt` l. 1311–1312, in §7 | **inexact**: the source reads «or even **the just** 2-rank»; the paper silently corrects a typo inside quotation marks — should be quoted as is or with [sic]. Minor |
| [IKKY22, Proposition 37] (Cayley graphs of `F_2^r` = quotients of cubes by codes) | l. 1343–1345 | correct |
| «determining the complete structure still seems out of reach at this moment» [GMMY24] | `GaoMarxKuoMcDonaldYuen…txt` l. 1168 (§5) | **exact** |
| «the Sylow-2 subgroup remains a mystery» [GMM19] | poster txt l. 14 | **exact** |
| [GMMY24, Remark 2.13] «We are not sure if that is a coincident, or a special case of some deeper connection» | l. 604–606 | **exact** (incl. their «coincident») |
| [GMMY24, Prop. 1.9] odd parts; [GMMY24, proof of Prop. 2.5] `u_i = x_i − 1`; [GMMY24, Prop. 2.12] F_2-rank of the folded cube; [GMMY24, §2.2] non-generic graphs from `Q_n/⟨𝟙⟩` | l. 220–225; l. 380–386; l. 542–544; l. ~538–541 | all correct |
| [GMMY24, Thms 4.1, 4.2; Conj. 4.14, 5.4]; [GMM19] `(n+1)`-th factor | see §2 (§9 entry) of this report | **exact** |
| «an analogous integral description … [could] explain … the remaining 2-primary factors» under an involution [Aky26, §4] | `TwoAdicAllOnesSquare…txt` l. 566–567, §4 «Further directions»: «Can an analogous integral description **with fixed vertices** explain both the folded all-ones class and the remaining 2-primary factors?» | **misleading use**: the ellipsis removes «with fixed vertices», and the preceding sentence says their reflections have fixed vertices «so the fold is not a regular double cover». The paper then writes «The fold law is such a description for the antipodal involution of the cube» — but the antipode has no fixed vertices (regular double cover), i.e. exactly the case Akyar et al. set aside. The sentence should be removed or rephrased («a description of this kind in the fixed-point-free case») |
| [Yue23] «non-generic» graphs | `Adinkras2rank…txt` l. 211: «non-generic in the sense of [14]» — Yuen attributes the term to GMMY (his [14]) | minor: credit GMMY for the term |
| [Lar24, §2] fusion rule of `V^{⊗2}`, reproduces the recursion | `Larsen…txt` l. 99–160 (§2); **my own check: 32/32 even n ≤ 64**, control fails 32/32 (`logs/larsen_check.log`) | correct |
| [TW21] characters | Larsen's [7] = Tubbenhauer–Wedrich, *Represent. Theory* 25 (2021) 440–480 — same data as the paper's [TW21] | correct |
| [RT14] exact sequence `0 → K(G^±) → K(G̃) → K(G) → 0` for double covers | `ReinerTseng…txt` l. 188–191 (Thm 1.2) | correct; RT14 §12.2 re-derives only Bai's **odd** part for cubes — no 2-part, no fold law |
| [DHS17] Ducey, Hill, Sin; [DEGJPP24] six authors | headers of the source files | correct |
| [VZ24], [LZ22] «give orders, not group structure» | see 4.2 | — |

### 4.2 References not in `material/sources/` (queries in `checks/QUERIES.md`, nos. 13–23)

| ref | used for | standard fact only? | bibliographic data |
|---|---|---|---|
| Bie93, Wil90 | credit: CSX use Bier's/Wilson's diagonal forms | yes (credit) | correct (EJC 14 (1993) 1–8; EJC 11 (1990) 609–615) |
| Don93 | tensor product theorem; Weyl/good filtrations | yes; explicitly «not used» | correct (Math. Z. 212 (1993) 39–60) |
| Jan03 | standard filtrations, lifting over complete rings | yes | correct |
| TW21 | characters of tilting modules of SL_2 | yes | correct (confirmed through Larsen's ref. [7]) |
| Kos66, Hum72 | Kostant's commutation formula (K) | yes, used correctly (checked in §2) | correct; Hum72 §26 is «Kostant's theorem» (Lemma 26.2 = (K)); Kos66 pages 90–98 not confirmed by my search |
| Str28 | uniqueness of the representation in `𝒦` (Lemma 10.13(a)) | yes, used correctly | correct |
| Kum52 | `κ(a,b) = v_2 C(a+b,a)` | yes | correct |
| vSt40, Cla40 | `v_2(B_{2m}) = −1` | yes, used correctly | correct |
| ABERS55, BBBB72 | PAVA / antitonic regression | yes | consistent (ABERS not found online by me) |
| Lor91, Big99, Kli18 | sandpile group basics | yes | correct |
| EL91 | the naming trap `FQ_m` | yes | correct; confirms «hypercube plus complementary edges» |
| OEIS A193134 | spanning trees of the folded cube | yes | **correct**: «Numbers of spanning trees of the folded cube graphs», a(2) = 1 (simple K_2), a(3..7) equal my eigenvalue formula (`logs/oeis_check.log`) |

Minor bibliographic remarks (PRESENTATION): [DHS17] is published (*Linear Algebra Appl.* 546 (2018) 154–168); [IKKY22]
is published (*Adv. Appl. Math.*); [Yue23] is published (*Electron. J. Combin.* 31(1) (2024) P1.38); [GMMY24] lacks
volume/pages. Optional: Anzis–Prasad (UMN REU 2016), the first upper bound for `c_1` and GMMY's ref. [1].

### 4.3 Priority (queries 1–12)

Searched: general web (extended mode), the arXiv API (sandpile/critical group × cube/hypercube/folded, newest
first), the Semantic Scholar citation tree of GMMY (3 citing papers), Reiner–Tseng, Sin's school, SL_2 tilting
literature, Anzis–Prasad. **I found nothing anticipating**: the whole 2-part of `K(Q_n)`; the fold law or the
sandpile group of the folded cube (only its spanning-tree count, OEIS, and its Laplacian spectrum are known); a
decomposition of any sandpile group over tilting modules; any proof of GMMY Conjectures 4.14, 5.4 or of the poster
formula. Caveat: like the authors, I did not search MathSciNet/zbMATH; my search is no more exhaustive than theirs.

### 4.4 §1.7 «Literature and priority», line by line

- Items 1–4 («what is ours»): consistent with my search (4.3).
- Item 5 (techniques as combinations): cannot be refuted by a search; reasonable.
- «What is not ours»: every attribution checked — Bai (odd part, Reiner's counts) ✓; GMMY (largest `n−1` factors,
  conjectures, Prop. 1.9, `u_i = x_i − 1`) ✓; CSX with Bier/Wilson ✓ (CSX cite both); RT14 ✓ (and indeed not used);
  tilting multiplicities from Donkin + TW21 ✓; Larsen reproduces the recursion ✓ (my own check, 32/32); standard
  filtrations [Jan03, Don93] ✓; Kostant ✓; classical tools ✓; Sin's school ✓. Missing but natural: GMMY's
  Proposition 2.12 is credited only in §10.8, not here (it is the F_2-rank half of the «mod-2 layer»); and
  GMMY's Remark 4.4 is essentially Lemma 9.2(b).
- «Contemporary context»: [VZ24] and [LZ22] indeed give orders, not structure ✓. **[Aky26]: the quotation is
  trimmed so as to change its meaning** (see 4.1): Akyar et al. ask for a description «with fixed vertices», i.e.
  for non-regular folds; the cube's antipodal fold is a regular double cover. The claim «The fold law is such a
  description» should go.
- The search statement (arXiv, journals, citation trees, no MathSciNet) is honest; I reproduced the Semantic Scholar
  tree of GMMY (3 papers).

## 5. The writing and the pdf

Line numbers refer to `material/paper/THE_DANCING_SAND_THEOREM_v1.md`; page numbers to the pdf (rendered with
`pdftoppm -r 80`, `scratch/pdf/p-NN.png`, all 39 pages looked at; zooms at 200 dpi where in doubt).

### 5.1 Claims in the abstract / §1.0 / §13 against the body

- Abstract and §1.0 state exactly what §8 and §10.8 prove — **no over-claim of mathematics** (the integer-shift GAP
  of §7 does not change any statement).
- §1.0 (l. 32) and §13 (l. 975): «the Main Theorem, Theorems D, O, F and DW were also read cold» / «Proved, with the
  grade "pencil, audited, read cold": … Theorems O and F; Theorem DW». But §12.3 (l. 971) says that **the printed
  proof of Theorem O (top bits) and the organization of §10 around 10.12/10.15 are new in this text**. So the grade
  «read cold» refers to earlier proofs, not to the ones printed. Should read: «Theorem O: new proof, pencil only
  (read cold for the first time here)»; same for §10 as organized. (The present reading is that first cold reading.)
- §1.5 item 4 (l. 128): «It is at most the valuation of one natural minor … The two bounds meet» skips Lemma 6.4: the
  natural minor gives the *natural* sums `U(r)`, and convexity is what turns them into the pooled sums `Y(r)`.
- §1.7: the [Aky26] sentence (l. 167) — see §4.1: the quotation is trimmed so as to change its meaning.
- §12.2 remark (l. 957) and §10.5 Remark (2) (l. 847): not reproduced (see §3.4) — a numerical claim stated more
  strongly than what was shown, attributed to an unpublished «flight».

### 5.2 Undefined symbols, symbols with two meanings, notation that changes

- l. 183: `Syl_2(Z ⊕ K)` is undefined (means `(Z ⊕ K) ⊗ Z_2`).
- l. 422 (proof of Prop. 5.4): the symbol `J` is never defined there (it stands for `i + o_D`); it is defined only
  later, in Lemma 9.8 (l. 669), and in §7.3 `J_H` is the carry-out set.
- **Heavy overloading** (the §1.6 table only acknowledges `D`, `K`, `T(·)`):
  `τ` = `Σ(h_t−2^t)` (§5.3, §9.2), window datum `τ_t` (§7.3), `τ_i = σ^{(1)}_i` (§10.1);
  `κ` = carries `κ(a,b)`, window count `κ_t` (§7.3), the map `κ_h` (Lemma 10.8);
  `σ` = Laplacian element, `σ^{(α)}_i`, saturation `σ_t`, the bijection `σ_r` and a generic matching `σ` (§6);
  `φ` = `x + v_2x` (§1.2), the lifting map `φ` (Lemma 3.2), the potential difference `φ(D)` (Thm 7.8 step 4);
  `ε` = `(−1)^j` (§10.2), `ε^2 = 0` in `𝒮` (§10.5), `ε_L` (Lemma 10.10); `h` = gaps `h_t`, level `h`, `h` in
  Cor. 3.4's proof, `h = (1+τ_M+a_M)/2` (Lemma 10.5); `c` = the shift (§10), `c = max I` (Lemma 7.7), the floor
  constant (§2.2), `c_D` (Prop. 9.5), `c_R` (Prop. 3.1(d)); `a` = antipode, `a_k(Δ)`, `a_n`, the constant of `𝒦`;
  `W` = windows, `W_±`, `W[a,b]`; `γ` = gold and `γ_{YX}`; `N` = a lattice, `2^{|I|}`, `N_±`; `L` = Laplacian, `L_r`,
  the glue matrix; `E` = hyperalgebra generator, a subset of `I`, the matrices `E, E'`, the variables `E_t`;
  `M` = final matrix, summands `M_j`, `M = T(ν)`. Each is locally clear, but a journal referee would ask for a
  cleaner notation, at least for `τ`, `κ`, `σ`, `φ`, `ε`.
- `max(x, ≤ G)` in the proof of Cor. 1.6 (l. 655–656) is informal notation.
- §2.2 (l. 191): «each weight space is then a direct summand» — tautological after «acts diagonally».
- The pdf renders `𝔞` (l. 863) as an ordinary italic `a` (p. 32, zoomed): the definition reads «`a: 𝒦 → Z_2,
  a + 2χ(2y) ↦ a`», indistinguishable from the antipode and from the constant `a` — a real rendering defect.

### 5.3 Small mathematical slips in the writing (no consequence)

- l. 376: «M has at most `(λ+1)/2` rows» — false when `λ + 1 = 2^{k+1} − 1` (`λ = 2`: 2 rows); correct bound
  `⌊λ/2⌋ + 1`.
- Lemma 4.5 proof (l. 359): «This is `−1` if `Δ = {m}`» — it is `+1` for `m = 0` (`a_0(∅) = −1`).
- Prop. 5.3 proof (l. 411): the final «difference» has the opposite sign (it is 0 anyway).
- Cor. 1.6 proof step 3 (l. 657): «`2(n−2) ≥ n` factors» — when `c_1 = G` one needs `n + 1`; true for `n ≥ 6`, and
  for `n = 4` one has `c_1 = 5 > G`; the text should say so.
- Lemma 6.4 proof, second case (l. 462): the reason for «some increment … is at most q» is missing (one line).
- IKKY quotation silently corrected inside quotation marks (§4.1).

### 5.4 Length, redundancy, style

- Not too long for its content; the proofs are compressed rather than padded. The main redundancy is §1.0 + §1.5 +
  the abstract, which is normal.
- Matrices are written as nested lists (`[[P, Q], [Q, P]]`, the λ = 6 example of §4.5 on one wrapped line, `glue`,
  `L`) — a journal would typeset them.
- Lemma K (inside the proof of Prop. 9.5) deserves a number; so does the «antisymmetry» paragraph of §7.1.
- Terminology: «dance», «doblar», «paso» (Spanish), «gold», «clocks», «rulers», «houses», «penalties», «turned lid»,
  «dry and wet». Charming and consistent, but a top journal will likely ask for neutral names, or at least an
  early glossary (the §1.6 table is close to one).
- §12–§13: honest about the process (AI constructors, audits, cold readers, no human referee, no formal proof), and
  the acknowledgement of AI use is clear. As journal material they are unusual: §12.1 and §12.3 describe internal
  roles («flights», «cold reader 1/2», «auditor») that a referee cannot inspect, and several §12.2 rows rest on
  them. 13 of the 26 rows of §12.2 have no control (§3.5). I would keep a short «Computations» section with
  reproducible code and move the process narrative to a supplement.
- «Every printed number was checked against an engine» (l. 971): every number I could test agrees (§3.2), except the
  Remark (2) thresholds.

### 5.5 The pdf, looked at rendered (39 pages)

No raw LaTeX anywhere; no cut or overflowing table; no section heading left alone at the foot of a page; the
bibliography renders fully (pp. 37–39). Defects found:
- p. 2 (§1.0 table): formulas broken inside cells («`coker(2^k` / `M(λ, i))`», «`a_n = 2^{n−2} −` / `2^{⌊(n−2)/2⌋}`»).
- p. 3 (§1.2): «Put `X(λ,` / `i) := …`» broken at the line end.
- p. 5 (Cor. 1.7 box): the exponent of `Z/2^{2^e+e−1}` is split, «`+ e − 1`» drops to the next line — easy to misread
  as `Z/2^{2^e}` followed by a stray term.
- p. 12 (§4.1): «`f_max`» renders as «`f_m ax`» (only `m` subscripted).
- p. 13 (Prop. 4.3 proof): «`rank/2`» appears in monospace code font inside prose.
- p. 14 (§4.5): the example matrix as a nested list on two wrapped lines.
- p. 17 (Thm 6.5 proof): the end-of-proof mark ∎ alone on a line.
- p. 32 (§10.7): `𝔞` rendered as `a` (see 5.2).
- p. 34 (Remark after §10.8): the exponent of `(−1)^{(n−H)/2}` wraps to the next line.
- p. 35 (§12.2 table): thin-spaced numbers broken across lines inside cells («`14` / `560`», «`22` / `500`»),
  «`hous-` / `es`».

## 6. The auditor's gates (§6 of the mission)

Opened only after §2–§5 of this report were written (DIARY). I read all six files in full and ran five of them
under the vigía (`rule_abs.py` is a library); none writes files or uses the network.

| gate | what §12.2 says | what the code checks | controls | ran (log) | their numbers vs mine |
|---|---|---|---|---|---|
| `rule_abs.py` | «the rule exactly as printed» | the rule of §1.2 (PAVA merging ties, ⌈⌉ first; multiplicities by the recursion) — identical in substance to my `engines/rule.py` | — | library | identical rule |
| `gate_direct.py` | Main Theorem vs direct Smith form, `n = 2..11`; DW vs direct Smith of `Q_n`, `Q_n/⟨𝟙⟩`; `x_1x_2` control | exactly that: min-valuation elimination mod `2^{31}` (correct; overflow-safe), one-free-summand self-check, `Q_n/⟨x_1x_2⟩` built by representatives | `x_1x_2` control **can fail** (it is printed, not counted in BAD); the rule itself has no control | `logs/gate_direct_11.log`: BAD 0, control fires n = 3..11 | **identical** to my Smith forms of cube and folded cube for every n = 2..11 |
| `gate_dance.py` | Theorem D (`λ ≤ 40`, `α = 1,2`, `i ≤ 6`, dim ≤ 64): 432/432; Thm 4.4 vs dance: 0 mismatches | exactly that (Fractions; dance on payment functions = Props 4.1–4.2) | the code ends with «# control: drop the factor 2^{o(Delta)}» but **no control is implemented** (it only prints valuations of `M(6,1)`) | `logs/gate_dance_40_6.log`: 432 ok, 0 mismatches | consistent with my `family_lattice.py` / `cells_smith.py` (larger ranges, controls that fail) |
| `gate_sections5to7.py` | Thm 7.8 «48 006 houses»; Prop 5.2·5.3·5.4: 109 200·14 560·301; Thm 7.10: 1 550 cells; Thm 6.2: «all I with \|I\| ≤ 4, every r: 61 cases» | Thm 7.8: (E), (M), (G), (Cut), (Λ), integer separation and the step-1 «walk» formula, three prices for `c_F` — but **48 006 are house-checks = 16 002 houses × 3 prices**, not houses. Thm 6.2: brute force over `I = range(s)` for **s ≤ 3 only**, plus six sets of size 2–3 → exactly 61 cases. **The §12.2 row «\|I\| ≤ 4» overstates the range: it is \|I\| ≤ 3.** The integer-shift hypothesis of Lemma 7.2(b) (no straddling) is not tested directly, only its consequence (the walk) | «no gold» and «`c_F = v'(I')`» controls **can fail** (fire in 164 and 24 houses); Thm O has no control | `logs/gate_sections5to7_127_3.log`: all counts as printed, 0 bad | consistent; my Theorem O check reaches `s ≤ 5` with controls; my Theorem F check covers all 43 690 houses `k ≤ 7`, `α ≤ 2` and adds the straddle detector |
| `gate_section9.py` | Cor 1.5·Lemma 9.6·Cor 1.6 `n ≤ 200`: 199·199·197; Props 9.3·9.4·9.5 `λ ≤ 300`: 300·292·22 500; Cor 1.7 `e ≤ 8` | exactly that, on the rule | «controls» are counters of cases where a stronger statement fails (`c_n ≠ G` in 37 n; the ceiling `g(n−i)` exceeded in 298 cells) — they can fire, but they are not pass/fail tests | `logs/gate_section9_200.log`: BAD none | consistent with my `check_rule_internal.py` (n ≤ 300) |
| `gate_section10.py` | weights `η_m, η'_m` (`m ≤ 39`); Lemma 10.1 (`n ≤ 6`); Lemmas 10.4, 10.5 and `X̄ ≅ 2X` on `T(λ)`, `λ ≤ 22`, `i ≤ 5`: 66+66+66+66, 132/132; controls 124/132, 66/66 | exactly that (Fractions; `X̄` as coker of `[τ | a−1]`) | sign-free fold and wrong sign in `Ψ_j` **can fail** (fire 124/132 and 66/66) | `logs/gate_section10_22_5.log`: all counts as printed | consistent with my `fold_family.py` (513 cells to `λ ≤ 63`) and `dance10.py` |

**Rows of §12.2 with no gate among the material:** Theorem 10.15 «covariance and `𝒦` at every level» (`≈ 10^6`
pairs) and its controls; Lemma 10.8 (2 862 entries); Lemma 10.20; Theorem 10.22 (flight 9); all «cold reader 1/2»
rows; the Remark (2) thresholds (flight 9). These cannot be checked from what the paper gives; my own engines cover
the substance of Lemma 10.8/10.12 (the final matrices of the dance), Theorem 10.15 (cleanliness), and the end-to-end
fold law, but **not the Remark (2) thresholds, which my engine contradicts** (§3.4).

**Where my numbers and theirs differ:** nowhere on a common quantity. All their printed counts are reproduced by
their own code; all their Smith forms equal mine. The differences are in what the table *says*: «\|I\| ≤ 4»
(really ≤ 3), «48 006 houses» (really house-checks), a control announced in a comment of `gate_dance.py` that does
not exist, and rows whose code is not provided.

## 7. Sealed predictions, hits and failures

Full register with times in `checks/SEALED.md`.
- S1–S8 (Part 1): **8 hits, 0 failures** (odds 75–97 %).
- S9 (Lemma 7.2(b) integer part false as stated, 95 %): **HIT** (`logs/lemma72b_counterexample.log`).
- S11 (no straddling where 7.2(b) is applied, k ≤ 7, 80 %): **HIT**. S12 (literal construction of V works, 88 %): **HIT** (`logs/theoremF_k7.log`).
- S13 (Smith(M) = Thm 7.10, 90 %): **HIT**. S14 (lattice T(λ) = Thm D + 7.10, 90 %): **HIT**. S15 (Theorem O count = 1, 97 %; control fails, 85 %): **HIT, HIT**.
- S16 (fold law per family, 92 %; control −a fails, 95 %): **HIT, HIT**. S17 (formal dance of Ψ_j, 85 %): **HIT**.
- **S18 (Remark (2): cleanliness fails with floor-dependent units for some l ≤ 31, 80 %; first at exactly 31, 50 %): FAILURE, FAILURE.** I believed the paper's remark; my engine finds the dances clean.
- S19 (odd part of Cor. 1.4, 95 %; control fails, 97 %): **HIT, HIT**. S20 (turned lid symmetry, 85 %): **HIT**. S21 (fold only for b = n, 85 %): **HIT**.
- S22 (Larsen's fusion rule reproduces the recursion, 90 %; control fails, 90 %): **HIT, HIT**.

**Balance: 22 sealed predictions (S1–S22, 30 graded parts): 28 hits, 2 failures (both parts of S18 — I believed
the paper's Remark (2), and my engine contradicts it).** The failures are printed above in the same type as the
hits. Calibration: my stated odds (50–97 %) were on the whole too low for statements of the paper and too high for
the one remark that rested on unpublished material.

## 8. My errors

1. `engines/check_rule_internal.py`, first run to n = 300: `top()` expanded `[e] * count` with counts of size
   about `2^n`; the vigía killed it at 2 GB after 6 s (`logs/rule_internal_300_100_300.log`, first version
   overwritten by the fixed rerun; the kill is recorded in `logs/DIARY.md`). Fixed by taking only what is needed.
   No result was affected.

2. My first control for Remark (2) of §10.5 (`engines/dance10.py` part (iv), `engines/dance10_controls.py`,
   `logs/dance10_controls.log`) used `payment + u(D)F` with no higher divided powers. Those are payment systems, whose
   dance is always clean (Prop. 4.1) — **a control that could not fail**. I caught it because every run came back
   clean, and replaced it by `engines/dance10_controls2/3/4.py` (with the tail `Σ_{m≥2}η_mF^{(m)}`, plus two
   negative controls that do fail). The faulty logs are kept, not deleted.
3. `engines/test_smithp.py`, first version: sympy's `smith_normal_form` on a `32 × 32` Laplacian blew up to
   1.26 GB; the vigía killed it at 7 s. Rerun with sympy only on `≤ 16 × 16` matrices. `engines/time1024.py`, first
   version: my recursive multiplicity function hit Python's recursion limit at n = 1024; fixed by warming the
   cache in increasing order. No result affected.
4. One syntax-only parse of `engines/dance10.py` was run outside the vigía (`python3 -c "ast.parse(...)"`, no
   computation). Recorded in `logs/DIARY.md`.

## 9. What I did not read

- **The paper:** I read every line of the markdown (1–1026) in order, and looked at all 39 pdf pages rendered at 80
  dpi (zooming at 200 dpi where in doubt). I did not proof-read the pdf text against the markdown character by
  character.
- **Statements I did not re-prove from scratch:** standard external facts used by the paper — Weyl's complete
  reducibility over Q, Strassmann's theorem, von Staudt–Clausen, Kummer, Legendre, existence/uniqueness of the
  antitonic projection, Smith form over a DVR — I checked that they are used correctly, not their proofs.
  Remark (1) after Theorem 3.6 (Donkin's identification) is declared unused and I did not verify it beyond the
  `p = 2` consistency check.
- **Sources:** I read the cited passages and their context in `material/sources/` (and Anzis–Prasad, Reiner–Smith
  abstract), not those papers in full. I did not consult MathSciNet/zbMATH, Google Scholar (only Semantic Scholar
  and the arXiv API), nor the journal versions behind paywalls. Kostant's page range and the ABERS record were not
  confirmed online.
- **Material the paper refers to but does not give:** the «flights», audits, cold readings 1–2, and the code behind
  the §12.2 rows on Theorem 10.15 (covariance/`𝒦`), Lemma 10.8, Lemma 10.20, Theorem 10.22 and the Remark (2)
  thresholds — not available to me (by design), hence unverified.
- **Machine ranges:** all my checks are finite (n ≤ 12 directly; families `λ ≤ 63/127`; houses `k ≤ 7`; dances
  `l ≤ 31`; Theorem O `s ≤ 5`). Beyond them I rely on the proofs as re-derived in §2.
- **The §3.5 claim about cold reader 1's `n = 13`** I judged plausible, not reproduced (my cap: one heavy job, 1.2 GB).

## 10. Files with md5

md5 computed through the vigía (`logs/md5_files.log`), after the final STATE line of `CLAUDE.md` was written.
- `REPORT_COLD.md` itself: its md5 is in the **last line of `logs/DIARY.md`** (it cannot contain its own hash).
- `logs/DIARY.md`: not listed (it changes with every entry, including the last one).
- `logs/md5_files.log` appears with the empty-file hash because it was being written when listed.
- `material/` is unchanged: all manifest md5 match at the start and at the end (`logs/manifest_check.log`,
  `logs/manifest_check_final.log`); a `material/.DS_Store` (macOS metadata) appeared, not written by me.
- The 45 pdf renders `scratch/pdf/*.png` are summarised by one aggregate hash (md5 of the sorted list of their md5).

```
8f935ea568f3c4c470948d46b329a435 CLAUDE.md
5b059b36cf13ab2476f22bf73fd4d193 checks/QUERIES.md
e92363e23b9eace2f518e5398f9be203 checks/SEALED.md
fa0c43cdda8bce8e8d1b6feef2e5d5a0 engines/cells_smith.py
34eb35191bf2034c38cbdd5bd0bd8f16 engines/check31.py
6f3c01764f7d5d42e78ce2328874fa48 engines/check_part3.py
31604617eccdb823258b0f710626129f engines/check_rule_internal.py
5ff580613f1b97461fc9428344cccde7 engines/dance10.py
856810356127427546c4f5594c96027d engines/dance10_controls.py
27eb5a0714996a49018945d731b7c8e7 engines/dance10_controls2.py
f24272f9bccdc24bf02b213817184d1f engines/dance10_controls3.py
4ab95ffdebabeb998613b87cf21ff340 engines/dance10_controls4.py
055d8a44634b54c24c50b4b2e5361b4d engines/example_n6.py
8f791f1a20cd1fe222f14b663b2b17cc engines/family_lattice.py
028cb6869185c4d9b6e3738322240b40 engines/fold_family.py
edd0a66a97c6ae0883274354187fd5a0 engines/larsen_check.py
ec848b4712e206f170c27244184abc42 engines/lattices.py
1172f56194d3bdfa959dc1f50d563406 engines/lemma72b_counterexample.py
adff1c5e849c312bf06b01c2bb697f5b engines/oeis_check.py
1857c5aaef4c46205dd2b1011e608ed4 engines/rule.py
aedbc9ee6de68b30ce10fa7dd7e80e1d engines/smith2.py
b92cf6d4f27ec31c1dd8b17aeb1ca8cb engines/smithp.py
9e6929c5128b20a65243d11ec7de326a engines/smithpy.py
c8e481907c2536b8eb27734caaa3aa0c engines/test_smith2.py
b24a4b8cf734c8e1f88fe75c75bab8a6 engines/test_smithp.py
7c260dd522b1ff41aecc93e57d26c971 engines/theoremF_check.py
a00cbebcaa98978297d655c5a2718113 engines/theoremO_brute.py
57b194db582e6dace1f561b7d146ebda engines/time1024.py
2daad4f40265c6a1872f1e370122e41f logs/cells_smith_127_30.log
1791efb00a13f1790888a451c9ac6ff4 logs/cells_smith_31_10.log
8732da22d9e7cb4a7c133bc00c6a950b logs/check31_10_11.log
2125f184b553bec907cdfab2f2c2273a logs/check31_12.log
be1795725bb9bb8338e9c672fa694412 logs/check31_1_9.log
5bd7ea07870aba714964df8e6fc0c109 logs/check_part3.log
31bb30eebdd760b27c7037a5a7f202e1 logs/dance10_15_3.log
7b1b5299467f1f9ddd6d3f041d27ca18 logs/dance10_31_3.log
b192dfd2806b389fe499f977c9e33bd8 logs/dance10_31_7.log
6efb046c249105cdd4e50af6d1c72c6c logs/dance10_controls.log
e8595ae828f29bbf113d37caddea8792 logs/dance10_controls2.log
a72c316e132fc9c27b5aef30c9d283c2 logs/dance10_controls3.log
dedf17d1d31a3c3a2de4a2835d38ed1a logs/dance10_controls4.log
cb31833ebc37f64ea4d1e4ee63231a85 logs/env_check.log
0278aefb46719fe7a18808f98e059f5c logs/example_n6.log
2bced2647a8a63a5a662f66d9e9e7f9c logs/family_lattice_31_10.log
4f45e430d2c9fab82ccc87b24aa9b117 logs/family_lattice_63_8.log
611c5b4b12ea07f6bfc9c98884de1a30 logs/fold_family_15_6.log
d17a260d5b0f3bb8c6465f55c9037f6b logs/fold_family_63_8.log
98fc4777d8178eaac35228bd0ccb5d78 logs/gate_dance_40_6.log
9031dc7cf5946096de07635604c6d781 logs/gate_direct_11.log
23c26f74ba993c1445a60bc6db90e8ea logs/gate_section10_22_5.log
b44f1754d155e30dae7dc778b54b0c50 logs/gate_section9_200.log
a9629d47fe7fdf4ad983aae6c0b53bb4 logs/gate_sections5to7_127_3.log
9a2127eceb68c8e51038b3283c7be278 logs/larsen_check.log
c207955df3f7e5e35fd0be73d0c68fae logs/lemma72b_counterexample.log
2720a895200b71e0753ddeb6978c21c2 logs/manifest_check.log
b8ef18f8924d05ecaa3fe4540ee631d3 logs/manifest_check_final.log
d41d8cd98f00b204e9800998ecf8427e logs/md5_files.log
22316c309f678158fcd807637179b441 logs/oeis_check.log
487ada2279d540b68dec723dcbcae28c logs/pdftoppm.log
cd43558ab461d74ed60a890a18f38a53 logs/pdftoppm_zoom12.log
cd43558ab461d74ed60a890a18f38a53 logs/pdftoppm_zoom12b.log
f0fefd8680e57929ab7c3e7942050a09 logs/pdftoppm_zoom14.log
6cd829c08051603ff6f0d19bbec606a5 logs/pdftoppm_zoom14b.log
27f54200d93ba08a7ca7f5726a7d6b5e logs/pdftoppm_zoom32.log
7c8d6268e64a40ddea8fba902370b0d5 logs/pdftoppm_zoom32b.log
76c0cfe6dae12b0c6df5bc11fe39f854 logs/pdftotext_anzis.log
33cb21d9068ffb0c0657b0a3ac62cbc9 logs/rule_internal_200_60_64.log
e41050ff65f678290a410c71dc1e470e logs/rule_internal_300_100_300.log
6bdbaee2849098fea627db3d12326515 logs/test_smith2.log
a099263c85cf7fd054324d5c0239ca60 logs/test_smithp.log
dce86f2197e3917d763d8c85c84ff2e2 logs/theoremF_k5.log
8720f28e14591ce2fd026cb0a7c17575 logs/theoremF_k7.log
15a5e92520642a43f83bc9aeb5bd90e5 logs/theoremO_brute.log
870e521fa67de61951781ebd44177f06 logs/time1024.log
58dbfc3896206a4e738d312a41d76c63 scratch/AnzisPrasad2016.pdf
0758db89bb61b8fcd9e50172f45e965f scratch/AnzisPrasad2016.txt
2185316bd5e5af320a8800f8ca9b165d scratch/md5_manifest.txt
2185316bd5e5af320a8800f8ca9b165d scratch/md5_now.txt
2185316bd5e5af320a8800f8ca9b165d scratch/md5_now_final.txt
ab473d9c9875d431b8376bbe1d469b27 scratch/smith_results_10_11.json
f8367aadf185ef9ad5484a4759a54061 scratch/smith_results_12_12.json
277ef39eba8102e7532ee10c768e5d5a scratch/smith_results_1_9.json
PNG renders (aggregate md5 of sorted per-file md5s):
5ca7a0e2027b09fc5ceb7cd5216126a5
45
```
