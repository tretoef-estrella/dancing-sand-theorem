# REPORT — «Grepy el volador 2», flight 2: THE TWO MOVES

## 0. First line — what this flight closes and what it does not

**This flight closes Leg 0 (Theorems Z, B, RT, S, E and λ = 2 re-derived: all CORRECT; one gap in RT's citation chain — tilting over Z_2, not only over F_2 — repaired), Leg A (P-R1 is now a THEOREM: an integral «doblar» functor Phi with `Phi(T(l)) = T(2l+1)` turns the halving of Theorem S into a proof for every odd family and every α), Leg B (the even step is a coupled two-dancer reduction; the natural uncoupled statement fails, first at λ = 2, i = 0), and Leg D's assembly: THEOREM D — the whole 2-part of K(Q_n), for every n, is the Smith form of explicit 2^{|I|} × 2^{|I|} matrices M(λ, (n−λ)/2) with closed-form entries (a polynomial recursion `q ← q² − y_t q` for the coefficients times products of room payments), with the small clocks (P-X1), the deficit law and every family with at most one lower binary digit PROVED. It does NOT close Leg C: for families with two or more lower digits the Smith form of M (the pooling of the closed rule) is measured — 4352/4352 cells against W^(α), 882/882 in tropical form, natural minors never cancel (2632/2632) — but not proved; the smallest uncovered cell is n = 6, λ = 6, i = 0. (Found on the way: the even step is two copies of the halved problem glued by 2^{−α} — `Ξ = L^{−1} diag(σ_A, σ_C) L` —, and at odd shifts with α = 1 the even families are exactly two copies of the halved family, 4064/4064 cells: the open step is a Hodge-versus-Newton computation for a diagonal operator on a glued lattice.) Hence Conjecture W and the trophies (Gao et al. 4.14 and 5.4, the poster's (n+1)-th factor) remain conjectures. P-R1 and Conjecture W never failed in any sealed cell (λ up to 63 per family, α up to 4).**

## 1. Leg 0 — second reading of the proved theorems

STATUS: CLOSED (10:52). Budget written before: 20 % of the flight (used: about 15 %). Every step below was re-derived by me, not stamped. Two of the pilot's gates re-run with my own code (`engines/lsmith.c`, `engines/dance.py`, `engines/gate1.py`; nothing imported from FLIGHT1): `logs/gate1b.log`, 7 PASS.

| theorem | the step that carries the weight (my words) | verdict |
|---|---|---|
| **Z** (extended Bier basis) | Pascal split `M_k(n) = M_k(n−1) ⊕ M_{k−1}(n−1)e_n` together with the ballot split `B_j(n) = B_j(n−1) ⊔ (B_{j−1}(n−1) + {n})`. Below the middle the type-(2) vectors ARE `0 ⊕ (basis of B)` (I checked `min(k−1, n−k) = k−1`), and type (1) mod B is `C_k(n−1)` (at k = n/2 because `B_k(n−1) = ∅`). Above the middle the j = μ vectors of type (1) supply exactly the classes of `B/B_0` through their second coordinate, which is itself a member of `C_{k−1}(n−1)`; the matrix against `A, B/B_0, B_0` is block triangular with identity blocks. The side condition `n ≥ 2j` for J ∋ n is automatic since `j ≤ μ ≤ n/2`. | **CORRECT** |
| **B** (stable floors) | U sends `η_{j,k}(J)` to `(k+1−j)η_{j,k+1}(J)` (handrail) and this lands inside `C_{k+1}(n)` as long as `k ≤ t−2 ≤ ⌈n/2⌉−1`, i.e. `k ≤ (n−1)/2`; then every chain reaches floor t−1 because `j ≤ n−(t−1)`. The ⊕Z: the image of `F_t` (t ≥ 1) lies in the augmentation ideal, so `R/(σR + F_t) = Z ⊕ K/F̄_t`. | **CORRECT** |
| **RT** (tilting reduction) | σ is a polynomial in F and H, so any isomorphism of (F,H)-modules carries σ to σ: coker σ splits along any decomposition of `V^{⊗n} ⊗ Z_2` as a module. The weight is in the decomposition `V^{⊗n} ⊗ Z_2 = ⊕ T_{Z_2}(λ)^{m_λ}`. | **CORRECT modulo citations, with one GAP in the citation chain (below)** |
| **S** (Steinberg) | (a) a bidiagonal matrix has the path as its bipartite graph, so every minor is 0 or ± a product of entries and the Smith form depends only on valuations; (b) the halving: for even s the subdiagonal `s+1` is a unit; substituting leaves the chain on `g_0, g_2, …` with diagonal valuation `2α + 1 + v_2(⌈j/2⌉ + t)` and subdiagonal `1 + v_2(t+1)`. I re-derived both. | **CORRECT** (and now a special case of P-R1, Leg A) |
| **E** (even = halved odd) | on `M ⊗ V`, `σ = τ ⊗ 1 + 1 ⊗ σ_V`; the relations `τx·b0 + x·b1`, `(τ+2)x·b1` eliminate `x·b1` with unit pivots and leave `M/τ(τ+2)M`. I re-derived it for every α (τ + 2^α) and for any floor payment π (then the operator is `ττ'`, `τ' = F + π(D+1)`, and τ, τ' commute only when π is linear). | **CORRECT** |
| **λ = 2** | `f = e10 − e01` is an eigenvector; Schur complement leaves `[[4i(i+1), 0], [4(i+1), 4(i+1)(i+2)]]`; the off-diagonal entry has the least valuation. I redid it for every α: `X^(α)(2, i) = {α+1+v(i+1), 3α−1+v(i(i+1)(i+2))}` (gate G2a, α ≤ 4). | **CORRECT** |
| rank F mod 2 = dim/2 | Donkin's factorisation; F acts only on the untwisted factor V or V⊗V, of rank half. | **CORRECT** |

**RT — which facts of tilting theory are cited, and do they hold at p = 2 over Z_2.** The proof in FLIGHT1 uses, in this order:
1. `V^{⊗n} ⊗ F_2` is tilting (tensor products of tilting modules are tilting). For SL_2 and V this is elementary: `Δ(m) ⊗ V` has a Δ-filtration with factors `Δ(m+1)`, `Δ(m−1)`, and dually.
2. **(the GAP)** The proof then says «Hom between modules with Weyl and good filtrations is free and commutes with reduction, so the endomorphism ring reduces onto `End(V^{⊗n} ⊗ F_2)`». This needs `V^{⊗n} ⊗ Z_2` itself to have a Δ_{Z_2}- and a ∇_{Z_2}-filtration **over Z_2**, which FLIGHT1 does not state. It is true and elementary for SL_2: the submodule of `Δ_Z(m) ⊗ V` generated by `v ⊗ b0` has the Z-basis `F^(r)v ⊗ b0 + F^(r−1)v ⊗ b1` (primitive vectors, so it is saturated) and is `Δ_Z(m+1)`; the quotient is Z-free of rank m, generated by a highest weight vector of weight m−1, and its Z-basis is the images of `F^(s)v ⊗ b1 = F^(s)(v ⊗ b1)`, s < m (since `F^(m)v ⊗ b1 ≡ −F^(m+1)v ⊗ b0 = 0`), so it is `Dist_Z(U^−)·v'` = `Δ_Z(m−1)` by definition. The ∇-filtration follows because the standard form `<s_S, s_T> = δ` is contravariant (U^T = L = E), so `V^{⊗n}` is self-dual. **Repaired here.**
3. `Ext^1_{G_A}(Δ_A(λ), ∇_A(μ)) = 0` and `Hom_{G_A}(Δ_A(λ), ∇_A(μ)) = δ_{λμ} A`, and for M Δ-filtered, N ∇-filtered `Hom_{G_A}(M, N)` is A-free with `Hom ⊗ k = Hom_{G_k}(M_k, N_k)` (Jantzen RAGS II.4.13 and II.B; Andersen). These are proved there for any (Noetherian) base ring and any p; nothing special happens at p = 2 for SL_2.
4. A = Z_2 is complete, `End_{G_A}(M)` is a finite A-algebra: idempotents lift, and a lift of an isomorphism of reductions is an isomorphism (Nakayama). Hence the indecomposable tilting lattices are the unique lifts T_{Z_2}(λ). Standard commutative algebra; p-independent.
5. (implicit) G_A-modules that are A-free of finite rank are the integrable Dist_A-modules with a weight decomposition (Jantzen II.1.20). Used silently by FLIGHT1 and by me (my lattices are given by E, F, H).
6. Donkin's tensor product theorem `T(1 + λ0 + 2λ1) = T(1+λ0) ⊗ T(λ1)^[1]` at p = 2 for SL_2 (hypothesis p ≥ 2h − 2 = 2 holds).
**Verdict:** at p = 2 over Z_2 the cited facts apply; the only missing link (item 2: tilting over Z_2, not only over F_2) is elementary for SL_2 and is supplied above. No ERROR.

**My own gates (`logs/gate1b.log`, own code):** G0 my Smith engine (full minimal-valuation pivoting, a different algorithm from FLIGHT1's row scan) = flint's SNF on random non-singular matrices; G2b Theorem S (with α); G2a λ = 2 (with α); **G3 the 2-part of K(Q_n) for n = 2..10 computed directly on `V^{⊗n}` equals `Σ m_λ X(λ, (n−λ)/2)` computed on my dance models of T(λ)** — this re-runs the pilot's P-RT2 (cube from small models) with a different family of models (FLIGHT1 used Steinberg tensor products and extraction; mine are the exact T(λ) built by Φ and V⊗, no extraction). Every value also equals the table of `material/RETOS_AL_ALCANCE_v1.md` lines 22–30 (n = 2..10; compared by eye at 11:43, READING).

## 2. Leg A — the odd step

**STATUS: CLOSED (10:56). P-R1 is a THEOREM (PROVED by pencil, modulo the same tilting citations as Theorem RT, see Leg 0), gated: P-A1 1259/1259 cells (odd l <= 63, alpha = 1, 2, j <= 20; the pilot's 276 cells are among them), P-A2 441/441 (my Phi-models = FLIGHT1's Steinberg extraction, l + 2i <= 40), G3 (the cube n = 2..10 from the Phi-models = direct).**

The idea arrived while reading FLIGHT1 (before Leg 0 was done); it is written here at once (disk rule) and gated only after Leg 0.

### A.1 The integral «doblar»: the functor Phi — PROVED (pencil), gated (G1: sl_2 relations, characters, divided powers, l ≤ 40; G3; P-A2 441/441)

For a lattice N with an action of Dist_{Z_2}(SL_2) (E, F, their divided powers, weights), put **Phi(N) = b0 (x) N ⊕ b1 (x) N** (as a Z_2-module), weight of `b0 n` = 2m + 1 and of `b1 n` = 2m − 1 for n of weight m, and

  `F(b0 n) = b1 n`,  `F(b1 n) = 2 b0 (Fn)`,  `E(b0 n) = 2 b1 (En)`,  `E(b1 n) = b0 (Ω − H²) n`,

where `Ω = 4FE + (H+1)²` is the (integral) Casimir of N, so `Ω − H² = 2H + 1 + 4FE` on N.

(a) **sl_2 relations.** On `b0 n` (weight 2m+1): `EF − FE = (2m+1+4FE) − 4FE = 2m+1`. On `b1 n` (weight 2m−1): `EF(b1 n) = 4 b1 EFn`, `FE(b1 n) = b1 (2m+1+4FE)n`, difference `4(EF−FE) − 2m − 1 = 4m − 2m − 1 = 2m − 1`. ✓

(b) **Divided powers are integral.** `F^{2s}(b0 n) = 2^s b0 F^s n`, `F^{2s+1}(b0 n) = 2^s b1 F^s n`, `F^{2s}(b1 n) = 2^s b1 F^s n`, `F^{2s+1}(b1 n) = 2^{s+1} b0 F^{s+1} n`. With `(2s)! = 2^s s! (2s−1)!!`: `F^(2s) = F^(s)/(2s−1)!!` on both slots, `F^(2s+1)(b0 n) = b1 F^(s)n/(2s+1)!!`, `F^(2s+1)(b1 n) = ((2s+2)/(2s+1)!!) b0 F^(s+1) n`. Since Ω is central, `E^{2s}(b1 n) = 2^s ∏_{i<s}(Ω − (m+2i)²) b1 E^s n`, `E^{2s+1}(b1 n) = 2^s ∏_{i≤s}(Ω−(m+2i)²) b0 E^s n`, `E^{2s}(b0 n) = 2^s ∏_{1≤i≤s}(Ω−(m+2i)²) b0 E^s n`, `E^{2s+1}(b0 n) = 2^{s+1}∏_{1≤i≤s}(…) b1 E^{s+1} n`; dividing by the factorials leaves `E^(s)` or `E^(s+1)` of N times odd denominators. So Phi(N) is a Dist_{Z_2}-lattice.

(c) **Reduction mod 2.** Ω ≡ (H+1)² mod 4, so on `E^s n` (weight m+2s) `Ω − (m+2i)² ≡ (2s−2i+1)(2m+2s+2i+1) ≡ 1` mod 2. Hence mod 2: `F^(2s)`, `E^(2s)` act as `1 (x) F^(s)`, `1 (x) E^(s)`; `F^(2s+1)(b0 n) = b1 F^(s) n`, `F^(2s+1)(b1 n) = 0`, `E^(2s+1)(b1 n) = b0 E^(s) n`, `E^(2s+1)(b0 n) = 0`. These are exactly the formulas of `V (x) N̄^[1]` (on the twist only the even divided powers act, as the divided powers of N). So **Phi(N) ⊗ F_2 ≅ V ⊗ (N ⊗ F_2)^[1]**.

(d) **Phi(T(l1)) = T(2 l1 + 1).** Phi is an exact functor (on morphisms `1 ⊗ f`, which commutes with the defining formulas) and sends saturated submodules to saturated submodules. By hand: **`Phi(Δ(μ)) ≅ Δ(2μ+1)`** (basis rescaled by the odd numbers `(2t−1)!!`, `(2t+1)!!`; E matches because `(2t+1)(2μ−2t+1) = 2μ+1+4t(μ−t)`) and **`Phi(∇(μ)) ≅ ∇(2μ+1)`** (F: `2μ+1−2r` and `2(μ−r)`; E: `(2r+1)(2μ−2r+1) = Ω − H²` on `w_r`). So Phi(T_{Z_2}(l1)) has a Δ_{Z_2}- and a ∇_{Z_2}-filtration: it is tilting **over Z_2**, its reduction is `V ⊗ T(l1)^[1] = T(2 l1 + 1)` (Donkin, p = 2), indecomposable; by the facts 3–4 cited for Theorem RT (Leg 0: Hom between Δ- and ∇-filtered lattices is free and commutes with reduction; idempotents and isomorphisms lift over the complete ring Z_2), **Phi(T_{Z_2}(l1)) ≅ T_{Z_2}(2 l1 + 1)**. (Check: Phi(Z) = V.)

### A.2 Theorem P-R1 — PROVED (pencil, modulo the citations of RT), gated (P-A1 1259/1259)

**For every Dist_{Z_2}-lattice N, every α ≥ 1 and j ≥ 0: coker σ^(α) on Phi(N) at shift j ≅ (rank N units) ⊕ 2·coker σ^(2α) on N at shift ⌈j/2⌉.** With A.1(d): `X^(α)(2 l1 + 1, j) = (dim T(l1) units) ⊕ 2·X^(2α)(l1, ⌈j/2⌉)`.

Proof. Top weight of Phi(N) is 2 l1 + 1; at shift j the floor of `b0 n` is `j + 2f` and of `b1 n` is `j + 2f + 1` (f the floor of n in N). So `σ(b0 n) = b1 n + 2^α (j+2f) b0 n` and `σ(b1 n) = 2 b0 Fn + 2^α (j+2f+1) b1 n`. The first relations eliminate every `b1 n` with a unit pivot: `b1 n ≡ −2^α(j+2f) b0 n` (rank N units). Substituting into the second: the cokernel is `N / Z N`, `Z n = 2Fn − 2^{2α}(j+2f)(j+2f+1) n`. Now `(j+2f)(j+2f+1)/2 = (⌈j/2⌉ + f)·u_f` with `u_f` odd (`u_f = j+2f+1` for j even, `j+2f` for j odd). So `Z = 2(F − 2^{2α}(⌈j/2⌉ + D)U)`, U the floor-diagonal unit. Right-multiplying by U^{-1} and conjugating by the floor-scalars `s_{f+1} = −u_f^{-1} s_f` (they commute with every floor-scalar and turn `F U^{-1}` into `−F`) gives `−2(F + 2^{2α}(⌈j/2⌉ + D))`. Multiplying a matrix by 2 raises every Smith exponent by one (units become Z/2, Z stays Z). ∎

This is the halving of Theorem S, now for every family: Theorem S is the case `N = St_{k−1}` (Phi(St_{k−1}) = St_k).

**Corollary (the closed rule is carried by «doblar»).** The doubling identity `B^(α)(2μ+1, J) = 1 + B^(2α)(μ, ⌈J/2⌉)` holds (pair the 2μ+2 consecutive factors of `J…J+2μ+1`: each pair has valuation `1 + v_2(⌈J/2⌉ + r)`; and `v_2((2μ+1)!) = μ + v_2(μ!)`); Weyl factors `μ ↦ 2μ+1`, shifts `j + (λ−μ)/2 = j + 2·(λ1−μ1)/2`, digits `I ↦ I + 1`, `k ↦ k + 1`, so the transfers `next(t) − t` are unchanged; pooling commutes with adding 1; units of X^(2α)(λ1) become the new Z/2 layer. So **W^(2α)(λ1) ⟹ W^(α)(2λ1+1)**, for every λ1 (PROVED, given P-R1).

## 3. Leg B — the even step

**STATUS: CLOSED (11:26) — as a reduction theorem.** PROVED (pencil) and gated (P-B1 985/985, even λ ≤ 62, α = 1, 2): the even step is `X^(α)(2λ1+2, i) = (dim/2 units) ⊕ 2·coker[[F + π_A, 0], [κ, F + π_C]]` on `T(λ1)²`. **The natural statement fails:** the uncoupled version `(dim/2 units) ⊕ 2·[X^(2α)(λ1, ⌈i/2⌉) ⊕ X^(2α)(λ1, ⌈(i+1)/2⌉)]` (P-B0, sealed S3) fails in 197 of 527 cells; the smallest is **λ = 2, i = 0** (truth `{2, Z}`, naive `{3, Z}`; then λ = 2, i = 2: `{2, 5}` against `{3, 4}`). What holds is the coupled 2-slot statement, whose coupling `κ = −π(2f+1)` is the payment of the middle floor; iterating both steps gives the dance of Leg C. (My sealed guess «first failure at i = 2» was wrong: published in §7.)

### B.1 «dar un paso» after «doblar»: T(2 l1 + 2) = V ⊗ Phi(T(l1)) — PROVED (pencil), gated (P-B1 985/985)

By Theorem E (FLIGHT1) and A.1, `T(2l1+2) = V ⊗ T(2l1+1) = V ⊗ Phi(T(l1))`. Basis of `V ⊗ Phi(N)` over N: `A = b0⊗b0`, `B = b0⊗b1 − b1⊗b0`, `C = b1⊗b0`, `Dd = b1⊗b1` (each ⊗ n). Then `F(An) = Bn + 2Cn`, `F(Bn) = 2A(Fn)`, `F(Cn) = Dd n`, `F(Dd n) = 2C(Fn)` — two copies of Phi(N), one floor apart, coupled by `A ↦ 2C`. For any floor-payment π (operator `F + π(D)`, D the floor; σ^(α) is `π(d) = 2^α(i + d)`), with floors A: 2f, B, C: 2f+1, Dd: 2f+2, eliminating B and Dd (unit pivots, 2·rank N of them) leaves on `N_A ⊕ N_C`:

  `2 · [[ F + π_A(D), 0 ], [ κ(D), F + π_C(D) ]]`,  `π_A(f) = −π(2f)π(2f+1)/2`, `π_C(f) = −π(2f+1)π(2f+2)/2`, `κ(f) = −π(2f+1)`.

For σ^(α) at shift i: `π_A ~ 2^{2α}(⌈i/2⌉ + D)`, `π_C ~ 2^{2α}(⌈(i+1)/2⌉ + D)`, coupling `κ = −2^α(i + 2D + 1)` (a unit times 2^α if i is even, 2^{α+1}(⌈i/2⌉ + D) if i is odd). **So `X^(α)(2l1+2, i) = (dim/2 units) ⊕ 2·coker[[σ^(2α)_{⌈i/2⌉}, 0],[κ, σ^(2α)_{⌈(i+1)/2⌉}]]` on T(l1)², up to floor units.**
Check λ = 2 (l1 = 0, N = Z, F = 0): `2·coker[[2^{2α} i(i+1)/2, 0],[2^α(i+1), 2^{2α}(i+1)(i+2)/2]]` = `{α+1+v(i+1), 3α−1+v(i(i+1)(i+2))}` — FLIGHT1 C.6 for α = 1 and my hand computation for every α.

## 4. Leg C — the rule from the two steps

**STATUS: NOT CONCLUDED (11:34; reopened 11:35, closed again 11:41 as NO CONCLUYO, see C.7).** PROVED: the dance recursion (C.0, gated P-C0 3320/3320), **P-X1 (the layer statement: the number of factors of exponent ≥ a is dim T(λ)/2^a for a ≤ k) for every family**, the coefficient algebra and the deficit law (C.4, gated P-C1 5454/5454), the rule for every family with |I| ≤ 1 (C.1), the corner clock (C.3), the reformulation C.6. NOT PROVED: (C-b), the Smith form of M for |I| ≥ 2 — the pooling of adjacent violators. Measured without a single failure (P-W 4352/4352, P-C2 882/882, natural minors 2632/2632). The pooling does come out of the Smith form of the merged chains, as the mission expected (the final matrix M is exactly the merged chains, one row per Weyl factor), but its pencil proof needs the 2-adic «ruler» structure of the payments (C.6) and was not finished: AGOTADO for this flight.

### C.0 The dance as a recursion on (payments, couplings) — PROVED (pencil), gated (P-C0 3320/3320)
The class: operators on `N^{⊕r}` (r «dancers» = slots) that are lower triangular, `G = diag(F + π_s(D)) + Σ_{s>s'} K_{ss'}(D)` with floor-scalar payments π_s and couplings K. Both steps keep the class and produce exactly half the dimension as unit pivots and a factor 2 on the rest:
- **doblar** (N = Phi(N')): `π'_s(f) = −π_s(2f)π_s(2f+1)/2`, `K'_{ss'}(f) = −[π_{s'}(2f+1)K_{ss'}(2f) + K_{ss'}(2f+1)π_s(2f) + Σ_{s'<s''<s} K_{s''s'}(2f+1)K_{ss''}(2f)]/2`.
- **paso+doblar** (N = V⊗Phi(N')): each dancer s splits into (s,A), (s,C): `π_{(s,A)}(f) = −π_s(2f)π_s(2f+1)/2`, `π_{(s,C)}(f) = −π_s(2f+1)π_s(2f+2)/2`, `K_{(s,A)→(s,C)} = −π_s(2f+1)`, `K_{(s',A)→(s,A)}` = the doblar formula at (2f, 2f+1), `K_{(s',C)→(s,C)}` = the doblar formula at (2f+1, 2f+2), `K_{(s',A)→(s,C)} = −K_{ss'}(2f+1)`, `K_{(s',C)→(s,A)} = 0` (all divided by the common 2 already).
After the k halvings that take T(λ) to T(0) = Z (dim 2^{k+|I|} → 2^{|I|}), **X^(α)(λ, j) = ⊕_{h=2}^{k} (Z/2^{h−1})^{2^{k+|I|−h}} ⊕ 2^k·coker M**, with M the final 2^{|I|} × 2^{|I|} lower triangular integer matrix (`M_ss = π_s(0)`, `M_{ss'} = K_{ss'}(0)`). The first part is exactly the small clocks of P-X1: **P-X1 follows from the two steps** (once they are gated). The big clocks are k + the Smith exponents of M. Leg C = the Smith form of M.

### C.1 The final matrix M: windows (pencil, from the recursion) — PROVED for the diagonal and for |I| = 1
Write `π(d) = 2^α(j + d)`, d = 0..λ, for the payments of the top floor-chain. Number the dance steps t = 0, 1, …, k−1 from the top: step t is «doblar» if digit t of λ+1 is 0 and «paso+doblar» (a split into A, C) if t ∈ I. A final dancer s is a word in {A, C}^I; put `o_s = Σ_{t ∈ I, s_t = C} 2^t`.
- **Diagonal.** Each doblar halves a product of two consecutive payments, and the split sends A to floors (2f, 2f+1) and C to (2f+1, 2f+2): one floor of level t is 2^t floors of level 0. Hence by induction **`M_ss = ± ∏_{d ∈ W_s} π(d) / 2^{2^k − 1}`, `W_s = [o_s, o_s + 2^k − 1]`** (a window of 2^k consecutive floors). With C ↔ minus sign at t, `o_s = (λ − μ_s)/2` is the bottom floor of the Weyl factor Δ(μ_s) inside T(λ).
- **|I| = 1** (`λ + 1 = 2^k + 2^b`). After the split at step b, with P the payments of level b (`v(P(d)) = 2^b α + v(⌈j/2^b⌉ + d)` by the Steinberg count), the coupling evolves by `K' = −[π_A(2f+1)K(2f) + K(2f+1)π_C(2f)]/2`; the two products are the same monomial (A(2f+1) ∪ K(2f) = K(2f+1) ∪ C(2f) as floor sets), so `K^{(h+1)} = −π_A^{(h)} K^{(h)}`, and with m = 2^{k−b}: `M = [[a, 0], [κ, c]]`, `a = ∏_{d=0}^{m−1}P(d)/2^{m−1}`, `c = ∏_{d=1}^{m}P(d)/2^{m−1}`, `κ = ∏_{d=1}^{m−1}P(d)/2^{m−1−(k−b)}`. **The coupling misses exactly `k − b = next(b) − b` halvings: that is the transfer.** Its floors `[1, m−1]` (level b) are the floors of the lower Weyl factor Δ(μ₋), and `a·c/κ` covers those of Δ(μ₊).
- **Theorem (|I| = 1) — PROVED.** Smith(M) = `(min(v a, v c, v κ), v a + v c − min)`, and `min(v a, v c, v κ) = min(v κ, ⌊(v a + v c)/2⌋)`: if `v a ≠ v c` then `v(⌈j/2^b⌉) ≥ k−b` (otherwise `v(j_b) = v(j_b + 2^{k−b})`), so `v a − v κ = 2^bα + v(j_b) − (k−b) > 0` and likewise for c. With `k + v κ = B(μ₋, j + 2^b) + (k−b)` and `k + v a + v c − v κ = B(μ₊, j)` (Kummer: each block of 2^b consecutive factors has valuation `2^b − 1 + v(j_b + d)`, and `v(λ!) = 2^k + 2^b − 2 − b`), the clocks are exactly the rule P-H2 (pooling = the case `v κ > ⌊(v a + v c)/2⌋`, where `|v a − v c| ≤ 1`). The case j = 0 (Z on top) is the same computation with `v P(0) = ∞`.

### C.2 The shape of M for every |I| — MEASURED (symbolic, `logs/explore_sym.log`, l = 6, 10, 12, 13, 14, 22)
With symbolic payments `p_d` (sympy), **every entry of M is one monomial**: `M_{ss'} = c_{ss'} ∏_{d ∈ W_s ∩ W_{s'}} p_d`, `W_s ∩ W_{s'} = [o_s, o_{s'} + 2^k − 1]`, non-zero **iff `D(s') ⊆ D(s)`** (D(s) = the digits where s says C = minus sign): M is lower triangular for the Boolean order on the dancers, and the Boolean order is refined by `o_s` increasing = μ_s decreasing, the order of the rule's pooling. The coefficient `c_{ss'}` depends only on `Δ = D(s) \ D(s')` (translation invariance), has odd numerator `2^r − 1` and a power-of-2 denominator; `c_∅ = −2^{−(2^k−1)}`. So `M = X^{−1}·C·Y`, X, Y diagonal (prefix products of payments) and C = multiplication by `c(x) = Σ_Δ c_Δ x^Δ` in `Q[x_t : t ∈ I]/(x_t²)`, independent of j and α. (Not a Kronecker product: e.g. for λ = 14 the normalised `c(x)/c_∅ = 1 + 8x0 − 8x1 − 16x2 − 48x0x1 − 64x0x2 + 64x1x2 + 128x0x1x2`.)

### C.3 The coefficients and the valuations of M — MEASURED (`logs/explore2.log`, every λ ≤ 63)
- **Deficit law.** Writing `M_{ss'} = (odd)·2^{δ_Δ − |W_s∩W_{s'}| + 1}·∏_{W_s∩W_{s'}} π`, the deficit is **`δ_Δ = k − |Δ| − min Δ`** (`δ_∅ = 0`) for every Δ ⊆ I and every λ ≤ 63: it depends only on k and Δ, not on the rest of I. For |Δ| = 1 it is `k − 1 − t` (C.1). Hence, with `w(d) = v(π(d)) − 1 = α − 1 + v(j+d)`:
  **`v(M_{ss'}) = 1 + (k − |Δ| − min Δ) + Σ_{d = o_s}^{o_{s'} + 2^k − 1} w(d)`**, `Δ = D(s) \ D(s')`.
- **The corner entry is the lowest clock (PROVED from the deficit law).** For `s = I` (all minus), `s' = ∅`: the window `[o(I), 2^k − 1]` is exactly the floor set of the lowest Weyl factor `Δ(μ_min)`, `μ_min = 2^k − 1 − o(I)`, and `k + v(M_{I,∅}) = 1 + 2k − |I| − min I + Σ w = B(μ_min, j + o(I)) + Σ_{t∈I}(next(t) − t)` (the transfers telescope to `k − min I`; `v(μ_min!) = 2^k − 1 − o(I) − k + |I|`). In general `k + v(M_{ss'})` is the rule's clock of the lowest Weyl factor of `T(2^k − 1 + o(Δ))` placed at shift `j + o_s`.
- **Smith(M) is decided by the valuations alone** (MEASURED): replacing every entry by `2^{v}·(random odd unit)` never changed the Smith form, 1512/1512 (|I| ≥ 2, λ ≤ 63, j ≤ 12, 3 trials).
- **Tropical Smith (MEASURED, P-C2, `logs/explore3b.log`).** For 882 cells (|I| = 2..5, λ ≤ 63, j ≥ 1, α = 1, 2) the determinantal divisors of M (partial sums of its sorted Smith exponents) equal the minimum total valuation of an r-matching inside the support of M, for every r — and equal the sums of the r smallest clocks of the rule (minus rk). **So Leg C is reduced to two statements: (C-a) the deficit law from the recursion; (C-b) the minimal r-matchings of the weights `1 + δ_Δ + Σ_{[o_s, o_{s'}+2^k−1]} w` are the partial sums of the pooled rule, and the minimal minors do not cancel.**

### C.4 (C-a) The coefficient algebra and the deficit law — PROVED (pencil)
**(i) Every entry is one interval monomial.** Induction on the dance level h: `π_s^{(h)}(f)` is (coefficient)·∏ π over the window `[2^h f + o_s, 2^h f + o_s + 2^h − 1]` and `K_{ss'}^{(h)}(f)` is (coefficient)·∏ π over `[2^h f + o_s, 2^h f + o_{s'} + 2^h − 1]` (D(s') ⊆ D(s)). In the doblar formula the three kinds of terms `π_{s'}(2f+1)K_{ss'}(2f)`, `K_{ss'}(2f+1)π_s(2f)`, `K_{us'}(2f+1)K_{su}(2f)` are products over two ADJACENT intervals whose union is always `[2^{h+1}f + o_s, 2^{h+1}f + o_{s'} + 2^{h+1} − 1]`: the same monomial. In the split at digit t: `(s',A)→(s',C)` is `−π_{s'}(2f+1)` and `(s',A)→(s,C)` is `−K_{ss'}(2f+1)`, whose windows are exactly the new intersections. ∎
**(ii) The coefficient depends only on Δ = D(s) \ D(s'), and its generating function `c(x) = Σ_Δ c_Δ x^Δ ∈ Q[x_t]/(x_t²)` obeys `c ← −c²/2` (doblar) and `c ← −c²/2 − x_t c` (split at t), from `c = 1` at level 0.** Proof: in the doblar formula the coefficient of `(s, s')` is `−[2c_∅ c_Δ + Σ_{Δ = Δ1 ⊔ Δ2, Δi ≠ ∅} c_{Δ1}c_{Δ2}]/2 = −[c²]_Δ/2` (an intermediate dancer u ↔ the ordered decomposition `Δ1 = D(u)\D(s')`, `Δ2 = D(s)\D(u)`; `x_t² = 0` kills overlapping pairs), and the diagonal is `−c_∅²/2`; the split adds `−x_t c` (from `−π_{s'}(2f+1)` for Δ = ∅ and `−K_{ss'}(2f+1)` otherwise). ∎ Check (λ = 6): `c = −1/8 − x0/2 + x1/2 + x0x1`, as in `logs/explore_sym.log`.
**(iii) Normal form.** Put `c = −2^{1−2^h} q` and `y_t = 2^{2^t} x_t`. Then `q_{t+1} = q_t² − y_t q_t = q_t (q_t − y_t)` (y_t = 0 at a doblar), `q_0 = −1`, hence **`q_k = −∏_{t<k} (q_t − y_t)`** (`q_1 = 1 + y_0`, `q_2 = (1 + y0)(1 + y0 − y1)`; for λ = 14 this gives `1 + 8x0 − 8x1 − 16x2 − 48x0x1 − 64x0x2 + 64x1x2 + 128x0x1x2`, exactly the measured C.2). So
  **`M = −2^{1−2^k} · X'^{−1} A Y'`**, `A_{DD'} = a_k(D \ D')` (D' ⊆ D) = multiplication by `q_k(y)` in the monomial basis `y^D` — an integer **unitriangular** matrix —, `X' = diag(G(o_D)/2^{o_D})`, `Y' = diag(G(o_D + 2^k)/2^{o_D})`, `G(x) = ∏_{d<x} π(d)`.
**(iv) The deficit law: `v_2(a_k(Δ)) = k − |Δ| − min Δ` for Δ ≠ ∅ (and `a_k(∅) = 1`).** Write `a_t(Δ)` for the coefficient of `y^Δ` in `q_t`, m = max Δ, μ = min Δ. (1) At `t = m + 1`: `a_{m+1}(Δ) = −a_m(Δ \ {m})` (the square of q_m has no y_m); this is a unit if Δ = {m}, and by induction on |Δ| has valuation `m − (|Δ|−1) − μ = (m+1) − |Δ| − μ`. (2) For t > m: `a_{t+1}(Δ) = 2a_t(Δ) + 2 Σ_{unordered Δ = Δ1 ⊔ Δ2, Δi ≠ ∅} a_t(Δ1)a_t(Δ2)`; by induction each cross term has valuation `≥ 1 + (t − |Δ1| − min Δ1) + (t − |Δ2| − min Δ2) ≥ 1 + 2t − |Δ| − μ − m`, which exceeds `v(2a_t(Δ)) = 1 + t − |Δ| − μ` by `t − m ≥ 1`. So `v(a_{t+1}(Δ)) = (t+1) − |Δ| − μ`. ∎ This is P-C1 (5454/5454, λ ≤ 127) as a theorem, and it gives **every valuation of M in closed form**:
  `v(M_{DD'}) = 1 + (k − |Δ| − min Δ) + Σ_{d = o_D}^{o_{D'} + 2^k − 1} w(d)`, `w(d) = α − 1 + v_2(j + d)`.
**(v) Block recursion.** With `t* = max I` and `λ' = λ − 2^{t*}`: `M(λ, j) = [[M(λ', j), 0], [M_10, M(λ', j + 2^{t*})]]` (same windows, same a_k), the dancers without t* first.

### C.5 (C-b) Where the Smith form of M stands — partly PROVED, partly MEASURED (`logs/explore4.log`)
**Potentials.** `v(M_{DD'}) = ρ_D + κ_{D'} + δ(D \ D')` with `ρ_D = −W(o_D)`, `κ_D = 1 + W(2^k + o_D)` (`W(x) = Σ_{d<x} w(d)`; ρ non-increasing, κ non-decreasing along the o-order) and the purely combinatorial cost `δ(Δ) = k − |Δ| − min Δ` (∞ off the Boolean support). **The rule's naive clocks have the same potentials, crossed:** `u(D) − k = ρ_D + κ_{I\D} + ε(D)`, `ε(D) = s_2(μ_D) + Σ_{t∈D}(next(t) − t) − k` (PROVED: `B(μ, J) = s_2(μ) + 1 + S[o_D, λ − o_D]` because `v(μ!) = μ − s_2(μ)`, and `λ − o_D = 2^k − 1 + o(I \ D)`). In o-order the dancers are `D_0 = ∅, …, D_{N−1} = I` and `I \ D_i = D_{N−1−i}`.
**Facts:**
1. `ε(I \ D) = −ε(D)` (MEASURED for every I ⊆ [0,k), k ≤ 6, |I| ≤ 4; by hand for |I| ≤ 2).
2. **The natural minor.** Let `L_r` = the last r dancers and `F_r` = the first r. Then `Φ(L_r, F_r)` (min-cost perfect matching L_r → F_r for δ) `= Σ_{D ∈ L_r} ε(D)` (MEASURED 798/798, k ≤ 6, |I| ≤ 4; by hand |I| ≤ 2). Hence the natural minor's tropical value is **exactly the rule's unpooled partial sum** `U(r) = Σ_{i ≥ N−r} (u(D_i) − k)`.
3. δ is **not** Monge in o-order (3752/7588 quadruples): no free lunch from total positivity.
4. In real cells the optimal rows/columns leave (L_r, F_r) whenever the rule pools (334/334 pooled cells) and sometimes by ties.
5. **Pools are not dyadic blocks** (`logs/explore5.log`, λ < 256, α = 1, 2): sizes 2, 4 and (rarely) 6, and about a third straddle the middle of a sub-cube (λ = 10, j = 2: u = (13, 10, 12, 9) pools the dancers {0} and {1}). An induction that cuts the cube in dyadic halves cannot see them one half at a time.
6. **Two exact product laws for M** (PROVED from C.4(ii), the window bookkeeping being the same): one more doblar at the bottom, `λ̃ + 1 = 2^{k+1} + o(I)`: **`M(λ̃; j) = −½ M(λ; j) M(λ; j + 2^k)`**; one more split at the bottom, `λ̂ + 1 = 2^{k+1} + 2^k + o(I)`: **`M(λ̂; j) = [[−½ M_0 M_1, 0], [−M_1, −½ M_1 M_2]]`, `M_i = M(λ; j + i 2^k)`** (= `[[½M_0, 0], [1, ½M_1]]·diag(M_1, M_2)` up to signs) — the even step of Theorem E once more, now on the final matrices.
7. **The natural minors do not cancel** (MEASURED, `logs/explore6.log`): the δ-optimal perfect matching `L_r → F_r` is **unique** in 2632/2632 cases (k ≤ 7, |I| ≤ 5). Since the potentials are constant on `(L_r, F_r)`, uniqueness gives `v(det M[L_r, F_r]) = U(r)` for every j and α, hence `d_r ≤ U(r)` (step (i) below) — as soon as the identity of fact 2 and the uniqueness are proved by pencil.

### C.6 (C-b) reformulated: two diagonal scalings of one unitriangular matrix — PROVED (reformulation), 11:32
With `S[x, y] = Σ_{d=x}^{y} w(d)`: **`Smith(M) = 1 + Smith(N)`, `N = diag(2^{a_D}) · A · diag(2^{b_D})`**, `a_D = S[o_D, 2^k − 1]` (non-increasing in o-order), `b_D = S[2^k, 2^k + o_D − 1]` (non-decreasing, `b_∅ = 0`), A = multiplication by `q_k` (integer, unitriangular, `v(a_k(Δ)) = k − |Δ| − min Δ`). The rule reads **`PAVA(a_D + b_{I\D} + ε(D))`** (the Weyl interval of dancer D is cut at 2^k into its two pieces). **The 2-adic structure of the payments enters only here:** for `w(d) = α − 1 + v_2(i + d)`, every floor `d < 2^k` has `v(i+d) = v(i+d+2^k)` except the one floor `d* ≡ −i (mod 2^k)`, so
  **`b_D = (a_∅ − a_D) + e*·[o_D > d*]`**, `e* = v(i + d* + 2^k) − v(i + d*)`,
and if `e* ≠ 0` then `min(v(i+d*), v(i+d*+2^k)) = k`. Hence `N = 2^{a_∅}·(diag(2^{a}) A diag(2^{−a}))·diag(2^{e*[o_D > d*]})`: the column scaling is the mirror of the row scaling, up to one jump.
(For arbitrary monotone a, b the identity is false: |I| = 1, a = (10, 0), b = (0, 0), δ = 1 gives Smith (0, 10) against the rule (1, 9); such (a, b) are not realisable.)
**MEASURED (`logs/explore8.log`): even with `e* = 0` the statement is not purely combinatorial.** For random non-increasing integer sequences a (not coming from payments), `Smith(diag(2^a) A diag(2^{−a})) = PAVA(a_D − a_{I\D} + ε(D))` fails in 753 of 2275 trials (first: k = 3, I = {0, 2}, a = (2, 0, 0, 0): Smith (−2, 0, 0, 2), rule (−1, −1, 1, 1)); that a is not realisable (it would need v(i) = 2 and v(i+2) = 0). **So the proof of (C-b) must use the ruler structure of the payments**: over an aligned dyadic block `[y, y + 2^t)` the sum of w is `2^t α − 1 + v_2(⌈i/2^t⌉ + y/2^t)`; the |I| = 1 proof (C.1) used exactly «`v(x) ≠ v(x + 2^e)` forces both ≥ e». This is the precise shape of the missing step.

### C.7 Leg C reopened (11:35, real clock) — estimate: up to 90 minutes of pencil and small runs (< 1 min, < 100 MB each); stop at 10 minutes without traction
**C.7.1 Removing the lowest digit (PROVED, pencil).** By P-R1 we may assume `0 ∈ I` (λ even; the doblar steps only change α and the shift, and carry the rule). Then the dancers come in adjacent pairs `(D1, D1 ∪ {0})`, `D1 ⊆ I1 = I \ {0}`, and:
- `q_k = Q + y_0 R` with `Q = ±q'_{k−1}` the coefficient polynomial of the halved family `λ1 = (λ−2)/2` (digits `I1 − 1`, one variable sign-flipped, which is a ±1 diagonal conjugation), and `R = Q·∏_{s ∈ I1'} (2 + y'_s/q'_s) · 2^{k−1−|I1|}`;
- the floor weights pair up: `w(2d') + w(2d'+1) = w'(d')` with `w'(d') = 2α − 1 + v(⌈i/2⌉ + d')` (the weights of the halved family), so **the scalings of the D1-dancers are exactly those of the halved family**: `a_{D1} = a'_{D1'}`, `b_{D1} = b'_{D1'}`, and `a_{D1∪0} = a_{D1} − w(o_{D1})`, `b_{D1∪0} = b_{D1} + w(2^k + o_{D1})`.
- Hence, in pair blocks, **`N(λ) = [[N(λ1), 0], [U^{−1} N_R, U^{−1} N(λ1) Z]]`**, `U = diag(2^{w(o_{D1})})`, `Z = diag(2^{w(2^k + o_{D1})})`, `N_R = diag(2^{a'}) A_R diag(2^{b'})`.

**C.7.2 (MEASURED, `logs/explore9.log`).** (a) The block of the dancers without the digit 0 has the Smith form of the halved family: 832/832. (b) For |I| = 2 (λ < 128, j ≤ 32, α = 1) the optimal rows/columns of the r-matchings take only four shapes (in o-order indices 0..3): natural `(3|0), (23|01), (123|012)`; `(2|0), (23|01), (023|012)`; `(3|0), (13|01), (123|012)`; diagonal `(0|0), (01|01), (012|012)`. Pooling appears exactly when a diagonal entry enters.

**C.7.3 Two sealed tests on the rule itself (rule values, no Smith forms).** **P-C3 HELD 4064/4064:** for even λ, odd i and α = 1 the big clocks are exactly two copies of those of the halved family, `H(λ, i, 1) = 2 × (H((λ−2)/2, (i+1)/2, 2) + 1)` — so at odd shifts «dar un paso» after «doblar» just duplicates the dancers. **P-C4 FAILED** (its extension to α ≥ 2 with each clock split into `h + 2 − α, h + α`): about half of the cells fail, first λ = 4, i = 1, α = 2 (truth {10, 10}, predicted {9, 11}). At the matrix level the coupling of the two copies cannot be removed by block elimination (I checked: row and column operations reproduce a coupling of the same valuation), so P-C3 is not yet explained.
**C.7.4 The even step is two copies glued by 2^(−α) (PROVED, pencil, 11:43).** In B.1, `π_A(f) − π_C(f) = π(2f+1)(π(2f+2) − π(2f))/2 = 2^α π(2f+1)` for `π(d) = 2^α(i+d)`, so the coupling is `κ = −π(2f+1) = 2^(−α)(σ_C − σ_A)` with `σ_A = F + π_A`, `σ_C = F + π_C` (the F's cancel). Hence
  **`Ξ = [[σ_A, 0], [2^(−α)(σ_C − σ_A), σ_C]] = L^(−1) · diag(σ_A, σ_C) · L`, `L = [[1, 0], [2^(−α), 1]]`**:
over Z_2[1/2] the even step is just two copies of the halved problem; over Z_2 the cokernel is that of `diag(σ_A, σ_C)` on the glued lattice `Λ_L = {(x, z) : z − 2^(−α) x ∈ N}`. When `σ_A = σ_C` the gluing commutes with everything and disappears (`Ξ = diag(σ, σ)`): this is the mechanism behind P-C3 (odd i, α = 1, where σ_A and σ_C differ only by the units `2D−1`, `2D+1`); I did not turn it into a proof. Iterating, the final M is `𝓛^(−1)·diag(window products)·𝓛` with 𝓛 a unipotent product of such gluings: **(C-b) is the computation of the elementary divisors of a diagonal operator with respect to the glued lattice `𝓛 Z_2^N`** — a Hodge-versus-Newton problem (Newton slopes = the diagonal valuations `a_D + b_D`, Hodge = the rule). Recorded as the most promising route for the next flight.

**Verdict on the reopened leg (11:41, real clock): NO CONCLUYO.** The new facts (C.7.1–C.7.3) sharpen the shape of the missing step but give no proof of it.

**What would close (C-b):** (i) the natural minors do not cancel (then d_r ≤ U(r)); (ii) every r×r minor has valuation ≥ Y(r) (the sum of the r smallest pooled clocks); (iii) Y is the greatest convex integer-increment minorant of U. Then the convexity of Smith divisors forces `d_r = Y(r)`. Proved for |I| = 1 (C.1); open in general.

## 5. Leg D — assembly and trophies

**STATUS: NOT CONCLUDED for the trophies; the assembly theorem (Theorem D) is CLOSED.**

### D.1 Theorem D (the dance formula for the whole 2-part) — PROVED (pencil, modulo the tilting citations of Theorem RT), gated
For every n ≥ 1:

  **`Syl_2 K(Q_n) ⊕ Z_2 ≅ ⊕_λ [ ⊕_{a=1}^{k−1} (Z/2^a)^{2^{|I|+k−1−a}} ⊕ 2^k · coker M(λ, (n−λ)/2) ]^{m_λ(n)}`**,

with, for `λ + 1 = 2^k + Σ_{t∈I} 2^t`, `o_D = Σ_{t∈D} 2^t`, and `D' ⊆ D ⊆ I`:

  **`M(λ, i)_{DD'} = −2^{1−2^k} · a_k(D \ D') · 2^{o_D − o_{D'}} · ∏_{d = o_D}^{o_{D'} + 2^k − 1} 2(i + d)`** (0 if D' ⊄ D),

where `a_k(Δ)` is the coefficient of `y^Δ` in `q_k ∈ Z[y_t]/(y_t²)`, `q_0 = −1`, `q_{t+1} = q_t² − [t ∈ I] y_t q_t` (so `q_k = −∏_{t<k}(q_t − y_t)`), and `m_λ(n)` is the tilting multiplicity (fusion recursion / character peeling of FLIGHT1). `2^k·` raises every Smith exponent by k (zero pivots stay Z).
**Dependencies, every one named:** Theorem RT (FLIGHT1, with the citation gap repaired in Leg 0: Jantzen II.4.13, II.B, II.E; idempotent lifting); Donkin's tensor product theorem at p = 2 (characters, and `T(2l+1) = V ⊗ T(l)^[1]`, `T(2l+2) = T(2) ⊗ T(l)^[1]`); A.1 (`Phi(T(l)) = T(2l+1)`); Theorem E (`V ⊗ T(odd) = T(even)`); A.2 and B.1 (the two steps, pencil); C.0 (the recursion), C.4 (the coefficient algebra). **Gates:** P-A1, P-A2, P-B1, P-C0 (3320 cells), P-D1 (closed form = dance, 1778/1778), P-D2 (n = 33..40 = FLIGHT1's sealed cells), G3 (n = 2..10 directly).
**What it gives:** the 2-part of K(Q_n) for every n as the Smith forms of explicit integer matrices of size `2^{|I|} ≤ (λ+1)/2`, one per tilting family, with entries in closed form — no lattice of size 2^n or dim T(λ), no extraction. With P-X1 (now PROVED: the small layers come out of the k halvings, C.0) the only remaining unknown is the Smith form of M.

### D.2 What is proved of the closed rule (Conjecture W)
- **PROVED:** the small clocks (P-X1, every family); the big clocks of every family with `|I| ≤ 1` (Steinberg: Theorem S/P-R1; |I| = 1: C.1), for every shift and every α; the lowest big clock's entry `M_{I,∅}` = the rule's lowest naive clock (C.3); the deficit law (C.4); `W^(2α)(λ1) ⟹ W^(α)(2λ1+1)` (A.2): «doblar» carries the rule into itself.
- **NOT PROVED (the one missing step, (C-b)):** `Smith(M(λ, i))` = the rule's pooled big clocks minus k, for `|I| ≥ 2`. MEASURED: P-W 4352/4352 (λ ≤ 63, α ≤ 4), P-C2 882/882 (tropical form), and FLIGHT1's 1271 + 294 cells. **Smallest cell where the missing step is visible: n = 6, family λ = 6 (`7 = 4 + 2 + 1`, |I| = 2), i = 0** (T(6) occurs once in `V^{⊗6}`): there M(6, 0) has a zero top row (the Z) and a 3 × 4 block whose Smith form is not covered by any proof of this flight (it is measured: n = 6 agrees with the table). The first cell with i ≥ 1 is λ = 6, i = 1 (n = 8, multiplicity 6).

### D.3 Trophies
| statement | source | status after this flight |
|---|---|---|
| n-th factor (Conj 4.14) | Gao et al. arXiv:1912.06919 p. 18 (read in the original: «v2(cn(Qn)) = max{max_{x<n−1}(v2(x)+x), v2(n−1)+n−3}», data n ≤ 11) | **still a conjecture**; true for n ≤ 128 under Conjecture W (FLIGHT1) and for n ≤ 40 by Theorem D's cells; it needs the largest big clocks of families with |I| ≥ 2 |
| (n+1)-th factor | JMM poster 2019 (read: «for n ≥ 4 that c_{n+1}(Q_n) = max_{x<n−1}{v2(x) + x}») | **still a conjecture**, same reason |
| `Syl_2 K(Q_{2^k}) ≅ Syl_2 K(Q_{2^k−1})² × Z/2^{2^k+k−1}` (Conj 5.4) | Gao et al. p. 18 (read) | **still a conjecture.** Reduction (READING): `K(Q_{2^k}) ⊕ Z = coker σσ'` on `Z[(Z/2)^{2^k−1}]`, `σ' = σ + 2`, an extension of `coker σ` by `coker σ'`; the conjecture says the extension splits and `coker(σ+2) ≅ coker σ` with Z replaced by one cyclic factor (true at k = 2 by hand: `{1, Z, 3, 3}` → `{1, 6, 3, 3}`) |
None of the three becomes a theorem in this flight: each needs big clocks of families with |I| ≥ 2, i.e. step (C-b).

### D.4 Novelty — not claimed
I read in the original only what is quoted (Gao et al. arXiv:1912.06919 p. 18: Conj 4.14, 5.4; the JMM poster's (n+1)-th factor line). I did not search the literature on integral forms of the Frobenius twist (Lusztig's quantum Frobenius, Donkin's tilting theory over Z) or on tilting modules for SL_2 at p = 2; the functor Phi, Theorem D and the deficit law may exist in some form. No claim of novelty is made.

## 6. Rafa's images — which served

Translations sealed in `checks/SEALED.md` S0 before any measurement.

| image | verdict | what it became |
|---|---|---|
| 4, the dance («doblar» and «dar un paso» from T(0)) | **served — it is the architecture of the proof** | doblar = the integral functor Phi (A.1), and **P-R1 is a theorem**: doblar shifts every clock by one, doubles the payment (α → 2α), halves the shift (⌈j/2⌉) — exactly what the closed rule does (`W^(2α)(λ1) ⟹ W^(α)(2λ1+1)`). Dar un paso = V ⊗ (Theorem E), and paso+doblar (B.1) creates a new pair of dancers coupled by the payment of the middle floor. From T(0) the dance yields the final matrix M (one row per dancer = per Weyl factor) in closed form (Theorem D). For «dar un paso» the effect on the clocks is proved only for one lower digit (the coupling misses exactly `next(t) − t` halvings: that IS the transfer); for two or more the pooling is measured, not proved. |
| 2, binary, «en secado o en mojado, en el doble de horas» | **served** | dry = mod 2, where the Frobenius twist exists (`V ⊗ M^[1]`); wet = over Z_2, where Phi is the twist's integral form: `F(b1 n) = 2 b0 Fn`, so `F² = 2·F_N`; «o está o no está» = the pairing b0 ↔ b1 = the dim/2 unit pivots; «el doble de horas» = α → 2α. |
| 3, the hall of mirrors | **served** | (i) the mirror-fixed piece (tilting) is unique, which is what identifies `Phi(T(l))` with `T(2l+1)`; (ii) the complement–transpose `M^♯_{DD'} = M_{I\D', I\D}` has the same shape as M, and the naive clock of a dancer pairs its row potential with the column potential of its mirror `I \ D` (`u(D) − k = ρ_D + κ_{I\D} + ε(D)`, `ε(I\D) = −ε(D)`, C.5) — «la de arriba es el espejo de la de abajo» read literally on the final matrix. |
| 1, «un premio para cada cubo … no puede sobrar nada, ni faltar» | **served in part** | «un premio para cada cubo» = one big clock per dancer (row of M); «no puede sobrar nada, ni faltar» = each halving is exact (exactly dim/2 unit pivots, the rest exactly 2·(half problem)), which **proved P-X1** (the small layers) and the doubling identity of B; «el equilibrio» as the pooling (equal sharing) **did not become a proof**: it is the open step (C-b). |

## 7. Sealed predictions, hits and failures

All in `checks/SEALED.md`, each written with its time BEFORE the measurement.

| id | prediction | ended |
|---|---|---|
| S0 | translation of the four images; Conjecture W^(α) | used (§6); W^(α) **held** (P-W) |
| P-A1 | P-R1 on the dance models, odd λ ≤ 63, α = 1, 2 | **held** 1259/1259 (85 cells skipped for word size, counted) |
| P-A2 | dance models = FLIGHT1's Steinberg extraction, λ + 2i ≤ 40 | **held** 441/441 |
| P-B1 | the coupled even step, even λ ≤ 62 | **held** 985/985 |
| P-C0 | the dance recursion (π, K) → M gives X, λ ≤ 63, α ≤ 3 | **held** 3320/3320 |
| P-W | Conjecture W^(α), λ ≤ 63, α ≤ 4, j ≤ 16 | **held** 3175/3175 (direct), 4352/4352 (dance) |
| P-C1 | deficit law and Boolean support, λ ≤ 127 | **held** 5454/5454 (now PROVED, C.4) |
| P-C2 | tropical divisors of M = rule partial sums | **held** 882/882 |
| **P-B0** | the naive (uncoupled) even step fails, first at λ = 2, i = 2 | **it fails (197/527), but my «first at i = 2» FAILED: the first failure is λ = 2, i = 0** |
| P-D1 | closed form of M = dance matrix, λ ≤ 127 | **held** 1778/1778 |
| P-D2 | the cube n = 33..40 from the closed form = FLIGHT1's sealed cells | **held** 8/8 |
| P-C3 | even λ, odd i, α = 1: two copies of the halved family (+1) | **held** 4064/4064 (against my own expectation of a failure) |
| **P-C4** | the same for every α, each clock split into h + 2 − α, h + α | **FAILED** for α = 2, 3, 4 (first: λ = 4, i = 1, α = 2) |
**Kill criteria:** P-R1 never failed in a sealed new cell (λ = 41..63 included); Conjecture W never failed (α = 1 included, λ up to 63 per family).

## 8. My errors

- **E1 (10:51).** In gate1, test G1c («divided powers are integral on the dance models») demanded that F^r and E^r be divisible by r! over Z; over Z_2 only v_2(r!) matters (Phi uses odd denominators (2s+1)!! on purpose). 2110 false failures. Buggy log kept: `logs/gate1_BUGGY_E1.log`; the claim was not changed, only the test; re-run `logs/gate1b.log`: PASS.

- **E2 (11:04).** explore3 estimated at 300 MB was killed at 1.34 GB in the tropical part (P-C2). Cause: my sealed list for P-C2 included λ = 62, which has |I| = 5 (32 dancers), and my subset dynamic programming walks 2^32 column masks. Fix: the r-matchings are now computed by min-cost flow (successive shortest augmenting paths, exact for every r at once); the prediction is unchanged.
- **E3 (11:25).** explore6 estimated at 1 min took 418 s (70 % of the 10-minute cap): the subset DP over the columns F_r at |I| = 5 walks ~10^8 Python states. No kill, but a bad estimate; later runs of this kind are restricted to |I| <= 4.
- **E4 (11:35).** In REPORT.md I wrote clock times from my own sense of elapsed time (13:15, 13:50, 14:20, 14:25, …) instead of reading `date`; the real times (in `logs/DIARY.md`, written with `date`) are 10:31–11:35 for the whole flight so far. All times in this report were corrected from the diary at 11:35, and again at 11:41 because I repeated the slip twice (I wrote 11:37, 11:38, 11:50, 11:52 by guess); from now on every time is pasted from `date`. Consequence: I had marked (C-b) AGOTADO believing hours had passed; by the leg rule (ten minutes without traction) it was not exhausted, so Leg C is reopened (C.7).

## 9. Files with md5

(11:43; REPORT.md and logs/DIARY.md are still being written and are not listed. `logs/gate1.log` = `logs/gate1_BUGGY_E1.log` and `logs/explore3.log` = `logs/explore3_KILLED_E2.log` are the same runs, kept under both names; `engines/explore3.py` is the fixed version, the killed run used the subset-DP version. `engines/liblsmith.dylib` is compiled from `engines/lsmith.c` with `cc -O2 -shared -fPIC`.)
```
    8449a57b8ab9626854e63880a440071f CLAUDE.md
    9ad3af8dfbc189cab9a44dbe6475461c engines/dance.py
    5944272783d5c01358b783097a05a214 engines/explore10.py
    74b800b0e219849a8143f203941e4425 engines/explore11.py
    3f9da27d5283039ea80a7bfb907c5601 engines/explore2.py
    01796e1e09942270ad5e7029b073d053 engines/explore3.py
    5f3b66c6a982e5786f7662b790336bcd engines/explore4.py
    910888b02ebca6dc304b28eb8b46c4a5 engines/explore5.py
    af5678cb425f959b9dcd18083fa8952b engines/explore6.py
    386832ba8aecec0b7e2dda2e33df1bc1 engines/explore7.py
    1101ae86019555bcacb38465072a3817 engines/explore8.py
    c8d81dca1cd81b7e0e4f082f2ba29727 engines/explore9.py
    96141f96acd2ee9c4df4b006883df32c engines/explore_sym.py
    cdb323f88de9b0a3a3fc2d446939d8a9 engines/gate1.py
    aed368c9efa4e9adc6a4a1bff0629da8 engines/gate2.py
    6e68fb7c78a389ca62442284bc4ad314 engines/legB_naive.py
    4edb32b5ca698c3d7b54e50c273b5ffa engines/legD_formula.py
    b5051e7eb631864b1585f40339bc28e0 engines/refcmp.py
    fb5c804bd68d88d14026d0d255600632 engines/rulew.py
    1d8de85764c651411160f7af4080e4aa engines/lsmith.c
    34aa254b5b70cbc4350440f33cce8ddd checks/SEALED.md
    a026d61d300c95a507e998dc059eeb1f logs/explore10.log
    0d61d95736708833c7108c215f7208c0 logs/explore11.log
    4c556b0d37e45f7a5e6891125e1d6907 logs/explore2.log
    568bd1e633288adbe1ae3133929ad2c1 logs/explore3.log
    568bd1e633288adbe1ae3133929ad2c1 logs/explore3_KILLED_E2.log
    30207c5ebd6148e9fc5eaf8d4960393a logs/explore3b.log
    498ad1ead69029675ad661d53ed0a2f6 logs/explore4.log
    1d6fc7b2272a141478a79589c6c7fb26 logs/explore5.log
    e5c34a82ccd88a905702ccf5d4925d02 logs/explore6.log
    44d9965f0c8020034047156be3981d9b logs/explore7.log
    f01554339eee2532b252ad854ad89765 logs/explore8.log
    3821c4d45b8873b9d7c2511d8b4f7ad4 logs/explore9.log
    c5f122b05a3532d929aaad18819feb8a logs/explore_sym.log
    7b5878b8e0fd7aa1ba527ba8cea1d10a logs/gate1.log
    7b5878b8e0fd7aa1ba527ba8cea1d10a logs/gate1_BUGGY_E1.log
    28b6e91b2c05c8b40a0364328fe250aa logs/gate1b.log
    c881322b42e6fd531ea455281cf79a4e logs/gate2.log
    922e096caab77a98653cfad289c5d473 logs/legB_naive.log
    b53d83bf78d62df30fc5906e828f481e logs/legD_formula.log
    ba24595ec78f2921ac2cb9d83ca42fa8 logs/probe_mem.log
    444786f6dca503c0b91c699200c05f5c logs/probe_time.log
    b10d48d6481529fbd55c9c7beee569d2 logs/refcmp.log
```

## Runs (estimate written BEFORE each run)
| run | what | estimate | log | result |
|---|---|---|---|---|
| gate1 (first run) | own engine vs flint (G0); dance models l <= 40: sl_2, characters, divided powers (G1); lambda = 2 and Steinberg with alpha (G2); cube n = 2..10 direct vs models (G3) | 60 s, 300 MB | logs/gate1_BUGGY_E1.log | VIGIA-FIN-OK, 65 MB, 1 s; 6 PASS, 1 FAIL: G1c failed because MY TEST demanded divisibility by r! over Z (odd factors 3, 5 included) instead of 2-adically — error E1 (§8). |
| gate1b | same, G1c tests v_2 only | 60 s, 300 MB | logs/gate1b.log | VIGIA-FIN-OK, 68 MB, 0.6 s, **7 PASS, 0 FAIL** |
| probe_time | one Smith at dim 512 and 1024 | 20 s, 200 MB | logs/probe_time.log | VIGIA-FIN-OK, 77 MB; dim 512 in 0.03 s; u64 refused an exponent 60 at l = 62 (guard works); harmless exit 1 |
| gate2 | P-A1, P-B1, P-C0, P-W (sealed S1) | 2 min, 400 MB (≈ 6000 Smith forms, dims ≤ 1024, plus exact Python Smith of the 2^{|I|} matrices) | logs/gate2.log | VIGIA-FIN-OK, 53 MB, 56 s. **P-A1 1259/1259, P-B1 985/985, P-C0 3320/3320, P-W 3175/3175 (direct) and 4352/4352 (dance), 0 failures**; cells whose largest exponent would reach 118 bits were skipped and counted (85, 49, 670) |
| refcmp | P-A2: my models vs FLIGHT1 XTable(40) (reference run of tilt.py) | 30 s, 300 MB (FLIGHT1 models up to 2048) | logs/refcmp.log | VIGIA-FIN-OK, 235 MB, 2 s. **P-A2 HELD 441/441** (every l, i with l + 2i <= 40) |
| explore_sym | symbolic final matrix M (sympy) for l = 6, 10, 12, 13, 14, 22 | 30 s, 200 MB | logs/explore_sym.log | VIGIA-FIN-OK, 54 MB, 0 s: every entry a monomial (C.2) |
| explore2 | c_Delta table l <= 63; Smith(M) vs random units (|I| >= 2, j <= 12, 3 trials) | 60 s, 100 MB | logs/explore2.log | VIGIA-FIN-OK, 13 MB, 29 s: deficit law; 1512/1512 valuation-determined (C.3) |
| explore3 | P-C1 (deficit law l <= 127), P-C2 (tropical divisors = rule) | 3 min, 300 MB (l up to 127: |I| <= 6, M up to 64 x 64; DP over 2^16 masks for |I| = 4) | logs/explore3_KILLED_E2.log | **KILLED by the watchdog, memory, 1.34 GB at 26 s** (error E2, §8). P-C1 had finished: **5454/5454** |
| explore3b | same, P-C2 by min-cost flow | 2 min, 150 MB (Bellman-Ford on <= 66 nodes, ~1000 edges, <= 32 augmentations per cell, ~1600 cells) | logs/explore3b.log | VIGIA-FIN-OK, 12 MB, 4 s. **P-C1 5454/5454, P-C2 882/882** |
| explore4 | (C-b) combinatorics: eps antisymmetry, Phi(L_r,F_r) identity (k <= 6, |I| <= 4), Monge test, optimal (R,C) in real cells | 2 min, 200 MB | logs/explore4.log | VIGIA-FIN-OK, 11 MB, 0.4 s (C.5) |
| explore5 | pool shapes of the rule, l < 256, |I| >= 2, j <= 64, alpha 1, 2 (no Smith forms) | 30 s, 50 MB | logs/explore5.log | VIGIA-FIN-OK, 10 MB, 1 s: pools of size 2 (28228), 4 (1206), 6 (17); 9197 of 29451 are NOT dyadic blocks (e.g. λ = 10 pools the two middle dancers) |
| explore6 | (P2) uniqueness of the delta-optimal natural matching, k <= 7, |I| <= 5 | 1 min, 300 MB | logs/explore6.log | VIGIA-FIN-OK, 87 MB, **418 s** (estimate 1 min: error E3, the subset DP at |I| = 5 is 2^32-free but walks ~10^8 states in Python). **Unique in 2632/2632** |
| explore7 | explicit optimal natural matchings for 4 small (k, I) (brute force over permutations, r <= 15 only for |I| <= 3; |I| = 4 up to r = 8) | 30 s, 50 MB | logs/explore7.log | VIGIA-FIN-OK, 5 MB, 0 s. Pattern: for r = N/2^s the optimal natural matching is `D ↦ D minus its s top digits of I`; the rows whose image is missing from F_r drop further (to ∅ at the end) |
| legB_naive | P-B0 naive even step, even l <= 62, i <= 16 (rule values) | 5 s, 30 MB | logs/legB_naive.log | VIGIA-FIN-OK, 6 MB, 0 s: naive statement fails 197/527; first failure l = 2, i = 0 |
| legD_formula | P-D1 (closed form of M = dance, l <= 127), P-D2 (cube n = 33..40 from the closed form) | 2 min, 200 MB | logs/legD_formula.log | VIGIA-FIN-OK, 11 MB, 1.4 s. **P-D1 1778/1778, P-D2 8/8** |
| explore8 | e*=0 core with random monotone a, k <= 6, 2 <= |I| <= 4, 25 trials each | 2 min, 100 MB | logs/explore8.log | VIGIA-FIN-OK, 11 MB, 21 s: the purely combinatorial version FAILS in 753/2275 random trials (C.6) |
| explore9 | (a) even-o block of M(lambda) vs M(lambda1); (b) catalogue of optimal (rows, cols), |I| = 2, l < 128, j <= 32 | 1 min, 100 MB | logs/explore9.log | VIGIA-FIN-OK, 11 MB, 4 s: (a) 832/832; (b) only 4 patterns of optimal (rows, cols) for |I| = 2 |
| explore10 | P-C3 (rule values only), even l <= 254, odd i <= 63 | 10 s, 30 MB | logs/explore10.log | VIGIA-FIN-OK, 10 MB, 0 s: **P-C3 4064/4064** |
| explore11 | P-C4 (rule values), even l <= 254, odd i <= 63, alpha 1..4 | 20 s, 30 MB | logs/explore11.log | VIGIA-FIN-OK, 8 MB, 1 s: **P-C4 fails for alpha >= 2** |
