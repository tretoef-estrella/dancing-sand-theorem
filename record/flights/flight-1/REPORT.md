# REPORT — Mission 1 of «Grepy el volador»: THE LANDING (with Leg F, the hall of mirrors)

## 0. First line — what this flight closes and what it does not

**This flight closes Legs A, B, E and F and writes the landing exactly: Bier's unimodularity is proved (with a basis of every floor above the middle, and the stable floors hold exactly to t − 1 = ⌈n/2⌉), the whole weld of the two staircases is one block, the kiss matrix `[I ∩ J = ∅]·C(n−i−j, m−j)` (Theorem L), and — modulo standard tilting theory — the 2-part splits into tilting families, `Syl_2 K(Q_n) ⊕ Z_2 ≅ ⊕_λ X(λ, (n−λ)/2)^{m_λ(n)}` (Theorem RT), which computes the whole group to n = 40 exactly (n = 14..40 new, n = 14 confirmed directly) and shows that the fold law holds to n = 32 family by family.** **It does not prove the whole 2-part: inside each tilting module it gives a closed rule (Conjecture W: small clocks `(Z/2^a)^{2^{|I|+k−1−a}}`, and 2^{|I|} big clocks = the Weyl staircases' «rooms over handrail» plus transfers `next(t) − t`, pooled) that is proved only for the Steinberg families and λ = 2, and is otherwise a conjecture — one that held in every sealed test (1271 cells, n = 33..40 sealed before computation, 294 large-model cells) and agrees with every proved theorem and with Gao et al.'s Conjectures 4.14 and 5.4 for all n ≤ 128.** **In the hall of mirrors no isometry and no naive glued candidate welds (except at n = 3, where nothing needs welding); the weld is the indecomposable tilting module — the piece the transpose mirror leaves fixed — and the kiss needs the landing matrix only modulo 4 or 8.**

## 1. LEG A — pre-flight — STATUS: CLOSED

Engines (own code): `engines/smith2.c` (2-adic local Smith elimination over Z/2^32, Z/2^64 and, added later, Z/2^128, pivots by increasing valuation), `engines/grepy.py` (ring Z[(Z/2)^n] in the basis s_S, the matrices of sigma, theta = tau(tau+2)/2, f = 1 + tau - a'). Nothing imported from the auditor's `gh_ring.py`; the idea «valuation-ordered pivots, Z/2^K arithmetic» is the standard one and is also in his `smith2_np`.

**A.0 Engine gate — MEASURED, 5/5** (`logs/legA_2.log`): for n = 2..6 the 2-part of coker(sigma) from my engine in u32 and in u64 equals the 2-part of the Smith form computed by flint on the **reduced Laplacian in the vertex basis** (a different matrix, a different algorithm).

**A.1 The whole 2-part, n = 2..11 — MEASURED, 10/10** (`logs/legA_2.log`): the full ring (2^n x 2^n, sigma) and the halving (2^{n-1} x 2^{n-1}, C = R'/(2 theta), exponents of theta plus one) agree with each other and with the table of `material/RETOS_AL_ALCANCE_v1.md`; the number of cyclic factors is 2^{n-1} - 1 every time.

**A.3 The fold law, n = 3..11 — MEASURED, 9/9** (`logs/legA_2.log`): the 2-part of R'/(f) equals the 2-part of K(Q_n) with every exponent lowered by one and the Z/2's dropped.

**A.1 and A.3 at n = 12, 13 — MEASURED, 4/4** (`logs/legA3_1.log`): cube and folded cube equal the cells of `RETOS_AL_ALCANCE_v1.md` (n = 13 in 1.3 s and 3.5 s, peak 590 MB).

**A.2 The stable floors, n = 2..11 — MEASURED, 40/40** (`logs/legA2_1.log`): for every t with t - 1 <= n/2, K/F_t (+) Z = (+)_j coker(B_j(t))^{C(n,j) - C(n,j-1)}. Beyond the middle exactly **five** further hits: (n, t) = (3,3), (5,4), (7,5), (9,6), (11,7), that is **n odd and t - 1 = (n+1)/2**; every other case beyond the middle misses (n = 11, t = 12: chains {1:1045, ...} against the true {1:496, ...}, as the auditor reported). Leg B explains the five: the exact stable range is **t - 1 <= ceil(n/2)**.

## 2. LEG B — the stable floors — STATUS: CLOSED

Bier's unimodularity is **proved here, not cited**, by an induction on n that also gives a basis of every floor above the middle. The ballot-path leading-monomial argument of the Chaise (paper v10 §4) was tried and **does not apply as it stands** (B.5).

### B.1 Notation

- `[n] = {1..n}`; `M_k = M_k(n)` is the free Z-module on the k-subsets of `[n]` (floor k; `M_k = 0` for k < 0 or k > n). In the cube's ring, `e_K` is `s_K`.
- `eta_{j,k}(J) = sum_{K ⊇ J, |K| = k} e_K` for a j-set J (zero if k < j).
- **Ballot sets.** `J = {i_1 < ... < i_j}` is a ballot set (Frankl rank j) if `i_l >= 2l` for every l. `B_j(n)` is the set of ballot j-subsets of [n]; it is empty when 2j > n.
- `U e_K = sum_{x not in K} e_{K ∪ x}` (one floor up).

### B.2 Lemma (the handrail) — PROVED

`U eta_{j,k}(J) = (k + 1 - j) eta_{j,k+1}(J)`.

Proof. `U eta_{j,k}(J) = sum_{K ⊇ J, |K|=k} sum_{x not in K} e_{K∪x}`. A (k+1)-set L ⊇ J arises once for each x ∈ L - J, that is k + 1 - j times. ∎

### B.3 Theorem Z (the extended Bier basis) — PROVED (pencil) and MEASURED (gate)

**For every n >= 0 and every floor 0 <= k <= n, the family**

  `C_k(n) = { eta_{j,k}(J) : 0 <= j <= min(k, n - k), J ∈ B_j(n) }`

**is a Z-basis of M_k(n).** For k <= n/2 this is Bier's theorem (CSX Theorem 3.1: the matrix E_k is unimodular). For k > n/2 it is the same statement with j cut at n - k.

Proof, by induction on n. For n = 0, `C_0(0) = {e_∅}`. Let n >= 1 and split the k-subsets of [n] by whether they contain n:

  `M_k(n) = A ⊕ B`, `A = M_k(n-1)`, `B = M_{k-1}(n-1)·e_n` (we write `(a, b)`, and `eta'` for the vectors of [n-1]).

The ballot sets split in the same way: `J ∈ B_j(n)` with `n ∉ J` iff `J ∈ B_j(n-1)`; and `J ∋ n` iff `J = J'' ∪ {n}` with `J'' ∈ B_{j-1}(n-1)` and `n >= 2j`. Summing over supersets K ⊆ [n] by whether `n ∈ K`:

  (1) if `n ∉ J`: `eta_{j,k}(J) = (eta'_{j,k}(J), eta'_{j,k-1}(J))`;
  (2) if `J = J'' ∪ {n}`: `eta_{j,k}(J) = (0, eta'_{j-1,k-1}(J''))`.

Put `mu = min(k, n-k)`. The vectors of type (2) are `(0, eta'_{i,k-1}(J''))` for `0 <= i <= mu - 1`, `J'' ∈ B_i(n-1)`; the side condition `2(i+1) <= n` is automatic because `i + 1 <= mu <= n/2`. By induction, `C_{k-1}(n-1) = {eta'_{i,k-1}(J'') : i <= min(k-1, n-k)}` is a basis of B.

*Case k <= n/2.* Then `min(k-1, n-k) = k - 1 = mu - 1`, so the type-(2) vectors are exactly `0 ⊕ (basis of B)`. Modulo `0 ⊕ B`, a type-(1) vector is `(eta'_{j,k}(J), 0)` with `j <= k`, `J ∈ B_j(n-1)`. If `k <= (n-1)/2` this index set is that of `C_k(n-1)`. If `k = n/2`, `B_k(n-1) = ∅` (since `2k > n-1`), so j runs over `j <= k - 1 = min(k, n-1-k)`, again the index set of `C_k(n-1)`. By induction these vectors form a basis of A. A family whose image modulo a direct summand `0 ⊕ B` is a basis of A, and whose remaining members form a basis of `0 ⊕ B`, is a basis of `A ⊕ B` (block-triangular matrix, unimodular diagonal blocks).

*Case k > n/2.* Then `mu = n - k <= k - 1` and `min(k-1, n-k) = mu`: the type-(2) vectors span `B_0 = span{eta'_{i,k-1}(J'') : i <= mu - 1}`, and `B/B_0` has the basis of the classes of `eta'_{mu,k-1}(J'')`, `J'' ∈ B_mu(n-1)`. A type-(1) vector has `j <= mu`, and its second coordinate `eta'_{j,k-1}(J)` is itself a member of `C_{k-1}(n-1)`; modulo `B_0` it is 0 if `j < mu` and the basis class of J if `j = mu`. So modulo `0 ⊕ B_0` the type-(1) vectors are `(eta'_{j,k}(J), 0)` for `j < mu` and `(eta'_{mu,k}(J), [eta'_{mu,k-1}(J)])` for `j = mu`. The second family maps bijectively onto the basis of `B/B_0`; the first is `C_k(n-1)`, because `min(k, n-1-k) = n-1-k = mu - 1`, a basis of A by induction. Ordering the family as (type 1, j < mu), (type 1, j = mu), (type 2) against `A`, `B/B_0`, `B_0` gives a block-triangular matrix with unimodular diagonal blocks. (For k = n: A = 0, mu = 0, and the family is `{e_[n]}`.) ∎

**Corollary (ballot count).** Since `|C_k(n)| = C(n,k)` for every k, differencing gives `|B_j(n)| = C(n,j) - C(n,j-1)` for `2j <= n` (the ballot theorem, recovered).

**Gate B1 — MEASURED, 11/11** (`logs/legB_1.log`, flint exact determinants): `det C_k(n) = ±1` for every n = 1..11 and every floor k = 0..n (including every floor above the middle). B1b: the ballot counts, 11/11.

**Controls (each fires, as it should):**
- C1 (Wilson's undivided vectors `U^{k-j}e_J = (k-j)!·eta_{j,k}(J)`): `|det| = prod_j ((k-j)!)^{d_j} != 1` in all 12 cells tried, exactly as predicted.
- C2 (replace the ballot sets by the lexicographically first `d_j` j-sets): fires in 11 cells (det 0 already at n = 5, k = 2).
- C3 (replace `e_J` by the Specht product `prod (e_b - e_a)` over the bracket matching of J, the pair forms of the Chaise): fires in 16 cells; `|det| = n` at k = 1 (n = 2..5), 48 at (4, 2). So **the Specht lattice is not Bier's lattice** (B.5).

### B.4 The stable floors, with the exact range — PROVED (pencil) and MEASURED

**Theorem B.** Let `F_t` be the subgroup generated by the `s_S` with `|S| >= t`. For every `1 <= t <= ceil(n/2) + 1`,

  `K(Q_n)/F_t ⊕ Z ≅ ⊕_{j=0}^{t-1} coker(B_j(t))^{C(n,j) - C(n,j-1)}`,

where `B_j(t)` is the lower bidiagonal matrix on the floors `k = j..t-1` with diagonal `2k` and subdiagonal `k + 1 - j`.

Proof. `σ F_t ⊆ F_t`, so `R/(σR + F_t)` is the cokernel of σ restricted to the floors `< t` and projected there. On each floor `k <= t - 1` take the basis `C_k(n)` (Theorem Z). For `k <= t - 2 <= ceil(n/2) - 1` we have `k <= (n-1)/2`, so `min(k, n-k) = k` and `min(k+1, n-k-1) >= k`: every `eta_{j,k}(J)` of `C_k(n)` is sent by U to `(k+1-j)·eta_{j,k+1}(J)` with `eta_{j,k+1}(J) ∈ C_{k+1}(n)` (Lemma B.2), and D is the scalar k on floor k. On the top floor `t - 1` the U-image lies in `F_t` and is discarded. Every chain `(j, J)` that starts at a floor `j <= t-1` reaches floor `t - 1`: this needs `j <= n - (t-1)`, and if it failed we would have `t - 1 > n/2`, i.e. n odd and `t - 1 = (n+1)/2`, and then `j > (n+1)/2 = t - 1`, a contradiction. So in these bases the truncated σ is the direct sum of the chains `B_j(t)`, one for each `J ∈ B_j(n)`, and `|B_j(n)| = C(n,j) - C(n,j-1)`. ∎

**Answer to the mission's question («up to which t does the proof go?»).** Up to **`t - 1 = ceil(n/2)`**: one floor past the middle when n is odd. This is exactly the set of the 45 measured hits (40 with `t - 1 <= n/2`, plus the five `(n, t) = (3,3), (5,4), (7,5), (9,6), (11,7)`). For n even the first floor past the middle already fails in every measured cell (`t - 1 = n/2 + 1`, n = 2..10; `logs/legA2_1.log`), and the reason is visible in Theorem Z: the one-floor chains `j = n/2` (the ballot sets of size n/2) are sent by U to `eta_{n/2, n/2+1}(J)`, which is **not** in the basis `C_{n/2+1}(n)` (there `j <= n/2 - 1`). That is the landing.

### B.5 The ballot-path argument of the Chaise — tried; READING: it is the same index set, not the same lattice

- The ballot sets that index Bier's basis are the paths of the Chaise's Theorem 4.1 (up to reflection), and the bracket matching of B.3/C3 is the greedy matching of its step (ii). Same combinatorics.
- But the Chaise proves linear independence over every field of **products of pair forms** `prod (y_b - y_a)` through distinct leading monomials. Bier's vectors are **sums over supersets**; `eta_{0,k}(∅)` contains every monomial of floor k, so no monomial order gives them distinct leading terms, and the pair-form lattice is a different lattice (control C3: index n at floor 1). Theorem Z is therefore proved by the Pascal induction above, which uses the ballot recursion `B_j(n) = B_j(n-1) ⊔ (B_{j-1}(n-1) + {n})`, not by leading monomials.

## 3. LEG C — the landing — STATUS: NOT CONCLUDED (the landing is written exactly and reduced to tilting modules, PROVED; inside each module the rule is a CONJECTURE that survives every test, proved only for lambda = 2 and the Steinberg families)

### C.1 The weld is the tilting decomposition (reading R-T, sealed in S0/S1 before any number) — PROVED modulo standard tilting theory; MEASURED

**Dictionary (PROVED, elementary).** Let V = Z^2 with basis b0 (weight +1) and b1 (weight -1), F b0 = b1, F b1 = 0, E b1 = b0, E b0 = 0: the natural module of SL_2 over Z, with the divided powers F^(r), E^(r) acting on tensor powers. The isomorphism Z[(Z/2)^n] -> V^(x)n, s_S -> (b1 in the factors of S, b0 elsewhere), sends floor k to the weight space of weight n - 2k, U to F, the down operator to E, D to (n - H)/2, so

  `sigma = U + 2D = F + n - H`,   and   `eta_{j,k}(J) = F^(k-j) e_J` (Bier's vectors are divided powers).

sigma is an element of the algebra acting on V^(x)n, not an endomorphism of the module; but any isomorphism of SL_2-modules preserves F and H, hence carries sigma to sigma. **So coker(sigma) is an invariant of the module V^(x)n, and it splits along any decomposition of the module.** More generally, for a module M with weights <= c (same parity) put `sigma_c = F + (c - H)`.

**Theorem RT.** For every n >= 1 and j >= 0,

  `coker(sigma + 2j on Z_2[(Z/2)^n]) ≅ ⊕_lambda X(lambda, j + (n - lambda)/2)^{m_lambda(n)}`,   `X(lambda, i) := coker(F + lambda - H + 2i on T_{Z_2}(lambda))`,

where `T_{Z_2}(lambda)` is the indecomposable tilting module of highest weight lambda over the 2-adic integers and `m_lambda(n)` is the multiplicity of the tilting module T(lambda) in V^(x)n over F_2. In particular **`Syl_2 K(Q_n) ⊕ Z_2 ≅ ⊕_lambda X(lambda, (n - lambda)/2)^{m_lambda(n)}`**.

Proof. V^(x)n (x) F_2 is a tilting module (tensor products of tilting modules are tilting; V = T(1)). Over the complete DVR Z_2, a module that is free of finite rank and whose reduction is tilting is a direct sum of the unique lifts T_{Z_2}(lambda), with the multiplicities of its reduction: Hom between modules with Weyl and good filtrations is free and commutes with reduction, so the endomorphism ring reduces onto End(V^(x)n (x) F_2) and idempotents lift (Jantzen, *Representations of Algebraic Groups*, 2nd ed., II.E.19–E.22; Andersen). On a summand T(lambda) of V^(x)n, of top weight lambda, the floor is k = (n - weight)/2, so `sigma + 2j = F + n - H + 2j = (F + lambda - H) + 2(j + (n - lambda)/2)`. ∎ **Grade: PROVED modulo the cited standard facts of tilting theory (not re-proved here).**

**Characters in characteristic 2 (PROVED, standard).** Write `lambda + 1 = 2^k + sum_{i in I} 2^i` (k the leading binary digit, I the other digits). Then
- `ch T(lambda) = prod_{i<k} (e^{2^i} + e^{-2^i}) · prod_{i in I} (e^{2^i} + e^{-2^i})` (Donkin's tensor product theorem at p = 2 iterated; the product formula agrees with the recursion `T(1 + l0 + 2 l1) = T(1 + l0) (x) T(l1)^[1]` for lambda = 0..64, gate RT0a);
- the Weyl factors of T(lambda) are the Delta(mu) with `mu + 1 = 2^k ± 2^{i_1} ± ...` (all signs of the lower digits), each once: `2^{|I|}` factors (gate RT0b, lambda = 0..64);
- `m_lambda(n)` is obtained by peeling these characters off `(e + e^{-1})^n` (exact integer arithmetic).

**Explicit lattices (the rivets).** `St_k = Delta_{Z}(2^k - 1)` with basis `F^(r) v`, `F·F^(r)v = (r+1) F^(r+1)v`, is tilting over Z_2 (its contravariant form has the odd values C(2^k - 1, r)). Tensor products of St_k's are explicit tilting lattices; each with highest weight lambda contains T_{Z_2}(lambda) exactly once, and its other summands are known from characters. So **X(lambda, i) is computed from a lattice of dimension 2^{sum k} — at most a few thousand for lambda <= 32 — instead of 2^n.**

**Gates (sealed predictions S1; `logs/legC_rt_1.log`) — MEASURED:**
- RT0c: the model `St_1^(x)n` with sigma_c reproduces sigma + 2j in the basis s_S, n = 1..8, j = 0..3.
- **P-RT1 HELD:** X(lambda, i) from the cube models V^(x)lambda and from greedy Steinberg models agree in all 127 cells lambda <= 12, lambda + 2i <= 24; no extraction ever produced a negative multiplicity.
- **P-RT3 HELD:** for lambda = 2^a - 1 (a = 0..4), X(lambda, i) is the cokernel of the full Weyl chain (Bier's staircase continued to the roof, subdiagonal 1, 2, ..., lambda). For these families **there is no landing to weld**: T = Delta = nabla.
- **P-RT2 HELD, 12/12:** the whole 2-part of K(Q_n), n = 2..13, computed ONLY from the small Steinberg models (never from V^(x)n), equals the measured table, Z included.
- **P-RT4 HELD (new cell, zero freedom).** Sealed in S4 from the tilting route, then computed directly (Smith form of theta on Z[(Z/2)^13], 8192 x 8192, `logs/legA14_1.log`, 10 s, 284 MB): **Syl_2 K(Q_14) = {1:4032, 2:792, 3:364, 4:1, 6:64, 7:1848, 8:26, 9:64, 10:364, 11:546, 13:64, 14:26}**, 8191 factors. Exact agreement.

### C.2 The whole 2-part for n <= 32 (MEASURED by the tilting route; `logs/legD_tilt_32.log`, 0.5 s, 152 MB)

The tilting route needs lattices of dimension at most 2048 for n <= 32 (instead of 2^31). Every cell n = 2..32 has exactly 2^{n-1} - 1 cyclic factors (Bai's count, an independent check) and one Z. The cells n = 15..32 are new (n = 14 is new and directly confirmed). They are listed in Leg D with their checks against the literature.

### C.3 The shape of X(lambda, i): small clocks and big clocks (sealed S5; `logs/legC_X_31.log`, table in `work/X_L31_I40.json`)

Write `lambda + 1 = 2^k + sum_{t in I} 2^t` (t < k) and `dim T(lambda) = 2^{k+|I|}`.

- **P-X1 HELD, 1312/1312 cells (lambda <= 31, i <= 40) — MEASURED:** `X(lambda, i) = ⊕_{a=1}^{k-1} (Z/2^a)^{dim/2^{a+1}} ⊕ H(lambda, i)`, where the «big clocks» H(lambda, i) are exactly `2^{|I|}` cyclic factors (one per Weyl factor of T(lambda); one of them is Z when i = 0), all of exponent >= k. Equivalently: **the number of factors of exponent >= a is dim T(lambda)/2^a for every a <= k** — each binary layer halves (Rafa's image 4).
- **P-X2 HELD (every Steinberg cell, i = 1..40) — MEASURED:** for lambda = 2^k - 1, `H = Z/2^E` with `E = 2^k + k + v_2(q)`, q·2^k the multiple of 2^k in [i, i + 2^k - 1]. Equivalently `E = v_2(det of the staircase) - v_2(handrail product) = 2^k + v_2(i·C(i + 2^k - 1, 2^k - 1))`: the big clock is what the rooms pay divided by what the handrail carries, and by Kummer its excess `v_2(q)` is a count of carries.
- **P-X3 FAILED as sealed at i = 0 (31 cells), HELD for every i >= 1.** At i = 0 the determinant vanishes (the top weight pays 0); my sum rule skipped that weight and forgot the kernel correction. An error of statement, published as a failed prediction.

**Theorem S (the Steinberg staircase, PROVED by pencil).** For lambda = 2^k - 1 and i >= 1, `X(lambda, i) = ⊕_{a=1}^{k-1} (Z/2^a)^{2^{k-1-a}} ⊕ Z/2^{2^k + k + v_2(ceil(i/2^k))}`; for i = 0 the last factor is Z.

Proof. X(lambda, i) is the cokernel of the lower bidiagonal matrix with diagonal `2(i + s)` and subdiagonal `s + 1` (s = 0..2^k - 1). (a) *The Smith form of a bidiagonal matrix over Z_2 depends only on the valuations of its entries*: the bipartite graph of its non-zero entries is a path, a path has at most one perfect matching on any vertex set, so every minor is 0 or ± a product of entries. (b) *Halving.* Consider the family `C(alpha, j, m)`: 2^m generators, diagonal valuations `alpha + v_2(j + s)`, subdiagonal valuations `v_2(s + 1)`. For s even the subdiagonal entry is a unit, and the relation of g_s solves `g_{s+1} = -(a_s/b_s) g_s`: one unit Smith factor each, 2^{m-1} of them. Substituting into the relation of g_{s+1} (s + 1 odd) leaves a bidiagonal chain on the generators g_0, g_2, ..., with diagonal `-a_{2t+1}a_{2t}/b_{2t}` of valuation `2 alpha + v_2((j+2t)(j+2t+1)) = 2 alpha + 1 + v_2(ceil(j/2) + t)` and subdiagonal `b_{2t+1} = 2t + 2` of valuation `1 + v_2(t+1)` (no sums occur, only products, so valuations are exact). Every entry is now even: **`C(alpha, j, m) = (2^{m-1} units) ⊕ 2·C(2 alpha, ceil(j/2), m - 1)`** (2· raises every exponent by one). (c) Starting from `C(1, i, k)` and halving k times gives 2^{k-1} units, then 2^{k-2} factors 2^1, ..., one factor 2^{k-1}, and finally `2^k · C(2^k, ceil(i/2^k), 0) = Z/2^{k + 2^k + v_2(ceil(i/2^k))}`. For i = 0 the entry `v_2(0)` is infinite all the way down and the last factor is Z. ∎ (Gate: P-RT3 and P-X2, every Steinberg cell lambda <= 31, i <= 40.)

This is Rafa's binary image as a proof: each halving keeps half the floors, multiplies every clock by 2, and squares what the rooms pay.

**Why half of the factors are units (PROVED).** Modulo 2, sigma_c = F (all c - w are even). By Donkin's theorem iterated, over F_2 `T(lambda) = ⊗_{t<k} T(1 + d_t)^{[t]}` (d_t the binary digits of lambda + 1), and F acts only on the untwisted factor `T(1 + d_0)` (V or V (x) V), with rank half its dimension. So `rank F = dim/2`: exactly dim/2 of the Smith exponents of X(lambda, i) are 0 and dim/2 are >= 1 (counting Z). This is the first line of P-X1; the other layers are MEASURED.

### C.4 The big clocks: a closed rule (sealed S8, S9) — CONJECTURE, MEASURED on 1271/1271 cells

Notation: `lambda + 1 = 2^k + sum_{t in I} 2^t`; the Weyl factors of T(lambda) are `mu_s` with `mu_s + 1 = 2^k + sum_{t in I} s_t 2^t` (all signs s), sitting at shift `i + (lambda - mu_s)/2`; `next(t) = min{u ∈ I ∪ {k} : u > t}`.

1. **naive clock of a staircase:** `B(mu, j) = sum_{r=0}^{mu} (1 + v_2(j + r)) - v_2(mu!)` — what the rooms of Delta(mu) pay (diagonal 2(j + r)) over what its handrail carries (1, 2, ..., mu);
2. **transfer:** `u(s) = B(mu_s, i + (lambda - mu_s)/2) + sum_{t in I, s_t = -1} (next(t) - t)`;
3. **pooling:** order the Weyl factors by mu decreasing and make the sequence u non-increasing by pooling adjacent violators; a pool of p values with sum T becomes (T mod p) values ceil(T/p) and the others floor(T/p). At i = 0 the top value is Z and never pools.

**Conjecture H.** `H(lambda, i)` is the resulting multiset. Hence (with P-X1 and Theorem RT) the **whole 2-part in closed form**:

  `Syl_2 K(Q_n) ⊕ Z_2 ≅ ⊕_lambda [ ⊕_{a=1}^{k-1} (Z/2^a)^{2^{|I|+k-1-a}} ⊕ H(lambda, (n - lambda)/2) ]^{m_lambda(n)}`.

**Out of sample (sealed S10, S11 before computing):**
- **P-H4 HELD, 8/8:** the cells n = 33..40, written in `checks/SEALED.md` from the rule (md5 of the log recorded there) before any tilting computation of n >= 33, equal the tilting route exactly (`logs/legD_oos_2.log`).
- **P-H5 HELD, 294/294:** for 42 Steinberg tensor models with highest weight 32..63 (dimension <= 4096) and shifts 0..6, the 128-bit Smith form of sigma_c equals the rule summed over all tilting summands (every T(nu), nu <= 63, enters).
- **P-H6 HELD, n = 2..128:** the rule never violates Bai's count, Gao et al.'s Theorems 4.1 and 4.2, or the pencil note's proved layers (number of Z/2, Z/4 and of factors >= 8) (`logs/legD_far_128.log`). These are theorems, so this is a falsification test with no Smith form behind it.
- **P-H7 HELD, n = 2..128:** Gao et al.'s Conjecture 4.14 and the poster's (n+1)-th factor; Conjecture 5.4 at n = 4, 8, 16, 32, 64, 128.

**Status.** P-H2 (the case |I| = 1, sealed S8): **410/410**. P-H3 (the general rule, sealed S9 from the cells lambda = 6, 10, 12, 13, i <= 8): **1271/1271 cells** (lambda = 1..31, i = 0..40, including |I| = 4 with 16 big clocks; `logs/legC_Hrule.log`). The P-H1 attempt (shift the labelled clocks of T((lambda-1)/2)) FAILED in 91/615 cells, exactly where clocks pool. **Grade: CONJECTURE (measured, not proved).** In the language of the building: each staircase brings its own clock (rooms over handrail), the rivet moves `next(t) - t` units of 2 from the handrail into the clock of every staircase that takes the minus sign at digit t, and where a lower staircase's clock overtakes a higher one the rivet makes them share equally.

### C.5 The Frobenius reduction with doubled payment (sealed S12) — PROVED for Steinberg, MEASURED for every odd lambda <= 39

Put `sigma^(alpha) = F + 2^alpha·(floor)` (alpha = 1 is the cube) and `X^(alpha)(lambda, j)` its cokernel on T(lambda) at shift j.

**P-R1 HELD, 276/276 cells** (odd lambda <= 39, alpha = 1, 2, j <= 20; `logs/legC_frob2.log`): for `lambda = 2 lambda_1 + 1`,

  `X^(alpha)(lambda, j) = (dim T(lambda)/2 units) ⊕ 2·X^(2 alpha)(lambda_1, ceil(j/2))`.

For the Steinberg family this is exactly the halving step of Theorem S (PROVED). In general it is MEASURED: modulo 2, F kills the Frobenius-twisted factor of `T(lambda) = V (x) T(lambda_1)^[1]`, the unit pivots pair the two vectors of V, and what is left behaves like `T(lambda_1)` with the room payments squared (2alpha). This is the structural reason for the closed rule's recursive shape, and the natural route to a proof of Conjecture H: an integral version of Donkin's `T(2 lambda_1 + 1) = V (x) T(lambda_1)^[1]` for the operator sigma^(alpha), plus the even step `T(2 lambda_1 + 2) = T(2) (x) T(lambda_1)^[1]` (not yet formulated; for lambda = 2 it is the 2 x 2 computation of C.6).

### C.6 Small cases proved by hand

- **lambda = 2 (PROVED).** On `T(2) = V (x) V` with basis e00, e10, e01, e11 and f = e10 - e01 one has `sigma f = 2(i+1) f`; eliminating f and e11 leaves the matrix `[[4i(i+1), 0], [4(i+1), 4(i+1)(i+2)]]`, whose 2-adic Smith form is `(2 + v_2(i+1), 2 + v_2(i) + v_2(i+1) + v_2(i+2))` (the off-diagonal entry has the least valuation). So `X(2, i) = {2 + v_2(i+1), 2 + v_2 i + v_2(i+1) + v_2(i+2)}` (i >= 1) and `{2, Z}` (i = 0) — exactly what Conjecture H gives (naive clocks `2 + v_2 i + v_2(i+1) + v_2(i+2)` and `1 + v_2(i+1)`, transfer 1, no pooling).
- **Steinberg (PROVED):** Theorem S.

**Theorem E (even families are the halved odd ones) — PROVED, gated 117/117.** For odd ν and every i, `X(ν + 1, i) ≅ coker( τ(τ + 2) on T_{Z_2}(ν) )`, with τ = F + ν − H + 2i on T(ν) (equivalently coker(2θ), θ = τ(τ+2)/2: the pencil note's halving, read inside one rivet).
Proof. Over F_2, `V (x) T(ν) = T(ν + 1)` for odd ν (Donkin: `T(1) (x) T(1 + 2l) = T(1) (x) T(1) (x) T(l)^[1] = T(2) (x) T(l)^[1] = T(2l + 2)`); `V (x) T_{Z_2}(ν)` is a tilting lattice whose reduction is indecomposable, so it is `T_{Z_2}(ν + 1)`. For any lattice M with an endomorphism τ, the operator `τ (x) 1 + 1 (x) σ_V` on `M (x) V` (σ_V = F + 2·floor on V) has cokernel `M/τ(τ + 2)M`: write `M (x) V = M·b0 ⊕ M·b1`; the relations `τx·b0 + x·b1` and `(τ + 2)x·b1` give `x·b1 ≡ −τx·b0` and then `τ(τ+2)x·b0 ≡ 0`. ∎ (`logs/legC_halfsum.log`: odd ν <= 29, i <= 12.)

With P-R1 (odd families reduce, with doubled payment, to families of half the size) and Theorem E (even families are the halved odd ones), **every family is reached from T(0) by the two moves λ -> 2λ + 1 and λ -> λ + 1**; a proof of Conjecture W would need P-R1 as a theorem and its analogue for the operator τ(τ+2).

## 3b. LEG F — the hall of mirrors — STATUS: CLOSED (catalogue, welds and kiss done; one number, N_lock = 2 or 3, measured but not explained)

### F.1 The catalogue — formulas PROVED (one line each) and gated (`logs/legF_cat.log`, 53/53, n = 1..8)

`L = U^T` is the down operator; `D` the floor; `R = Z[(Z/2)^n]` in the basis s_S.

| mirror | what it does to sigma (exact) | isometry or distortion | welds? |
|---|---|---|---|
| transpose T (contravariant duality for <s_S, s_T> = delta) | `sigma^T = L + 2D`; swaps the Weyl staircase (U acts by 1, 2, 3, ...) with the dual one (..., 3, 2, 1) | isometry: coker(sigma^T) = coker(sigma) | no, by itself |
| complement c: s_S -> s_{[n]-S} | `c sigma c = sigma^T + 2(n - 2D)` (P-M1) | distortion `2(n - 2D)`: zero on the middle floor (n even), ±2 on the two middle floors (n odd) | the mirror that makes the upper half chains is **c composed with the dual basis** (F.2); with the true landing block it welds by construction |
| sign twist t: x_i -> -x_i (s_i -> 2 - s_i), ring automorphism | `t(sigma) = 2n - sigma`; P_t unitriangular with diagonal (-1)^{|S|} (P-M2) | isometry: K = coker(2n - sigma) | no; its glued candidate is the dual-Weyl one (F.3) |
| the group <c, t> | `(ct) sigma (ct)^{-1} = 2D - L`; **ct is unipotent and ≠ 1** for every n = 1..6, so **<c, t> is infinite dihedral**, not a small group (P-M3, against the auditor's expectation) | — | — |
| antipode a = x_1...x_n (multiplication) | `a sigma = sigma a`, `a^2 = 1`: on V^(x)n it is the group element g^(x)n, g = [[1,0],[-1,-1]] in GL_2(Z) | isometry of sigma; **the fold** (quotient by a - 1) is a distortion: K-bar ≠ K | the fold law is a statement about this mirror (D.4) |
| coordinate permutations pi | `pi sigma pi^{-1} = sigma` | isometry, fixes sigma | no (keeps floors) |
| Fourier (evaluation on characters), `H[K,S] = 2^{|S|}[S ⊆ K]` | `H sigma = diag(2|K|) H` | the most distorting: H is not unimodular | **no**: coker diag(2|K|) has 2-part `⊕_k (Z/2^{1+v_2 k})^{C(n,k)}`, of order 2^n times too large (P-M4), n = 2..8 |
| control `sigma^T + 2I` | — | — | a different 2-part at every n = 2..8 (P-M5 fires) |

**Lesson confirmed (Chaise):** T, t, a, pi are isometries and none of them, alone, says anything new. The two that carry content are c (distortion 2(n - 2D)) and the fold by a (distortion: K-bar).

### F.2 The landing, exactly: the kiss matrix — PROVED (pencil) and MEASURED

**Theorem L (the landing).** Let m = floor(n/2). On the floors `k <= m` take Bier's basis `eta_{j,k}(J)` (j <= k, J ballot). On the floors `k >= m+1` take `w_{i,k}(I) = c(eta*_{i,n-k}(I))`, the complements of the **dual** Bier basis of floor n - k (i <= n - k, I ballot). Both are Z-bases (Theorem Z). In these bases sigma is:
- diagonal `2k` on floor k;
- below: `U eta_{j,k}(J) = (k+1-j) eta_{j,k+1}(J)` (k < m) — Bier's staircases;
- above: `U w_{i,k}(I) = (n-k-i) w_{i,k+1}(I)` (k >= m+1; zero when i = n - k) — the mirrored staircases, coming down from the roof;
- **one block of contact**, from floor m to floor m + 1:
  - n even: `U eta_{j,m}(J) = sum_{(i,I)} (m - i)·G[(i,I),(j,J)]·w_{i,m+1}(I)`, with **`G[(i,I),(j,J)] = [I ∩ J = ∅]·C(n-i-j, m-j)`**;
  - n odd (n = 2m+1): `U eta_{j,m}(J) = (m+1-j) sum_{(i,I)} G1[(i,I),(j,J)]·w_{i,m+1}(I)`, with **`G1[(i,I),(j,J)] = [I ∩ J = ∅]·C(n-i-j, m+1-j)`**.

Proof. Below: Lemma B.2. Above: `U c = c L`, and the dual of the handrail lemma, `<L eta*_{i,l}(I), eta_{i',l-1}(I')> = <eta*_{i,l}(I), U eta_{i',l-1}(I')> = (l - i') delta`, gives `L eta*_{i,l}(I) = (l - i) eta*_{i,l-1}(I)` for floors l <= m; with l = n - k this is `U w_{i,k} = (n-k-i) w_{i,k+1}`. Contact: the coefficient of `w_{i,k}(I) = c(eta*_{i,n-k}(I))` in a vector x of floor k is `<x, c(eta_{i,n-k}(I))>` (c is an orthogonal involution and eta, eta* are dual); for `x = eta_{j,k}(J)` this pairing counts the k-sets K with `K ⊇ J` and `[n] - K ⊇ I`, which is `[I ∩ J = ∅]·C(n - i - j, k - j)`. With n even, n - m = m, floor m has both bases, and `U w_{i,m} = (m - i) w_{i,m+1}`; with n odd, `U eta_{j,m} = (m+1-j) eta_{j,m+1}` and the pairing is taken on floor m + 1. ∎

**Gates (`logs/legF_land.log`):** `sigma B = B S` with S built from these formulas and B the basis matrices (flint exact inverses for the dual bases), **n = 2..11, 10/10**, every B unimodular; coker S = Syl_2 K(Q_n), **n = 2..12, 11/11**. The kiss matrix G (n even) or G1 (n odd) is **unimodular**, **n = 2..12, 11/11** (sizes up to 924 x 924) — as it must be, being a change of basis.

**What the kiss looks like.** `G[(i,I),(j,J)]` is non-zero only when **I and J are disjoint**: a ballot set J meets its mirror image only through the sets that avoid it. In particular the "diagonal" (I = J ≠ ∅) of G is **zero** (gate, 11/11): the mirror never returns a staircase to itself. The only diagonal survivor is `G[∅,∅] = C(n, m)`. The weights are binomials `C(n-i-j, m-j)` whose 2-adic valuations are Kummer carries (the central ones `C(2r, r)` have `v_2 = s_2(r)`, the number of binary ones of r).

### F.3 Which mirrors weld — the glued candidates (`logs/legF_cand.log`, `logs/legF_floors.log`)

The candidates, each a direct sum of one chain per ballot set (floors j..n-j, diagonal 2k), glued face to face at the landing:
- **Delta** (Bier's staircase continued to the roof, handrail 1, 2, ..., n-2j: no mirror);
- **nabla** (the staircase coming down from the roof, handrail n-2j, ..., 2, 1: mirror T, and also mirror t, whose glued candidate is the same up to transpose and reversal);
- **c** (Bier below, the c-dual image above, **identity landing** G = I): this is exactly S(G) with G replaced by I (consistency gate, 11/11);
- **cdist** (Bier below, the literal complement image above, with the distorted diagonal 2 min(k, n-k));
- **H** (Fourier: diag(2|K|)).

| n | truth | Delta | nabla | c (identity weld) | cdist | H |
|---|---|---|---|---|---|---|
| 2 | {2:1} | {1:2, 2:-1} | same | {1:1, 2:-1} | {1:1, 2:-1} | {1:2} |
| 3 | {1:1, 3:2} | **welds** | **welds** | **welds** | {2:2, 3:-2} | fails |
| 4 | {1:2, 3:4, 5:1} | {1:2, 2:3, 3:-1, 5:-1} | same | {2:2, 3:-4, 4:3, 5:-1} | = c | fails |
| 5 | {1:6, 3:4, 4:1, 6:4} | {1:-1, 2:1, 3:1, 4:-1} | same | {3:1, 4:-1} | {3:-4, 4:4, 5:4, 6:-4} | fails |
| 6 | ... | {1:14, 2:-3, 3:-1, 5:5, 6:-5} | same | {1:5, 2:-4, 3:-1, 5:-4, 6:4} | ... | fails |
| 7 | ... | {1:-6, 2:6, 4:6, 5:-6} | same | {4:6, 5:-6, 7:-6, 8:6} | ... | fails |
| 8..12 | ... | fails | same | fails | fails | fails |

(defect = candidate minus truth, as {exponent: multiplicity}; full rows in the log.) **MEASURED, n = 2..12.**

- **None of the naive welds works, except at n = 3** (and trivially n = 1). My sealed P-L2 said «none, for every n >= 2»: **it FAILED at n = 3**. The reason is exact and is the tilting picture: `V^(x)3 = T(3) ⊕ T(1)^2` and both are Weyl modules (Steinberg weights), so at n = 3 there is nothing to weld; n = 1 and n = 3 are the only n <= 16 with this property (`logs/legC_mult.log`).
- **Delta and nabla have identical defects in every cell** (MEASURED, n = 2..12): the two staircases, continued naively, fail in exactly the same way.
- **Floor by floor (the identity weld against the truth, truncations K/F_t):** they agree for every t <= ceil(n/2) + 1 (Theorem B) and the first defect appears on the first floor above the landing: t = n/2 + 2 for n even; for n odd at t = (n+3)/2 + 1 (n = 5, 9) or one floor later (n = 7, 11); never at n = 3. Example n = 8, t = 6: truth {1:49, 2:1, 4:42, 6:27}, identity weld {1:49, 2:1, 3:14, 5:48, 7:7}.
- **The mirror that welds is c composed with the dual basis, with its own landing block, the kiss matrix G** (Theorem L): it welds by construction, because it is a change of basis. Every other mirror of the catalogue is either an isometry (says nothing new) or gives a wrong group.

**«Isotype by isotype» — the answer is that the true group does not split by isotypes.** Over Z_2 it splits by tilting families (Theorem RT), and a non-Steinberg family T(lambda) welds `2^{|I|}` isotypes together (the Weyl factors Delta(mu), mu + 1 = 2^k ± lower binary digits of lambda + 1). The multiplicities differ: e.g. n = 8 has `T(8)x1, T(6)x6, T(4)x14, T(2)x8` against the isotypes `Delta(8)x1, Delta(6)x7, Delta(4)x20, Delta(2)x28, Delta(0)x14` (`logs/legC_mult.log`). A mirror can weld «isotype by isotype» only where the family is Steinberg (lambda + 1 a power of 2): there T = Delta = nabla and Bier's staircase continued to the roof is already exact (P-RT3).

Two facts read off the multiplicity table (MEASURED n <= 16; the first has a one-line proof): `m_lambda(2k) = m_{lambda-1}(2k-1)` (because `V (x) T(lambda) = T(lambda+1)` for odd lambda, Donkin), and `m_1(n) = 2^{(n-1)/2}` for odd n (READING, n = 1..15).

### F.4 The kiss (K1, K2, K3) — `logs/legF_land.log`, `logs/legF_kiss.log`

**K1, touching the mirror (n even) — PROVED and MEASURED.** On the middle floor (n even) the distortion 2(n - 2D) of c vanishes, and there Bier's basis and the complement of its dual meet on the same floor. Theorem L says the whole landing **is** the kiss matrix `G[(i,I),(j,J)] = [I ∩ J = ∅]·C(n-i-j, n/2-j)`: everything else is staircases. Gate: S(G) gives the true group for n = 2, 4, 6, 8, 10, 12 (and odd n with G1). So yes: read exactly on that floor, the gluing rule gives the whole landing. **But it gives it as a matrix, not as a formula for the group**: the Smith form of S(G) is what C.3–C.4 describe (shape measured, closed rule conjectured).

**K2, the breath on the glass (n odd) — MEASURED, n = 3, 5, 7, 9, 11.** «Removing the breath» = giving the floor m + 1 the diagonal 2m of floor m (so that c maps the two middle floors onto each other without distortion). Results:

| n | breathless group | K(Q_n) |
|---|---|---|
| 3 | {1:1, 2:2} | {1:1, 3:2} |
| 5 | {1:6, 4:4, 5:1, 7:4} | {1:6, 3:4, 4:1, 6:4} |
| 7 | {1:28, 2:9, 3:6, 4:14, 5:6} | {1:28, 2:1, 4:8, 5:6, 6:14, 7:6} |
| 9 | {1:120, 2:10, 6:16, 7:26, 8:48, 9:26, 11:1, 13:8} | {1:120, 2:10, 4:16, 5:26, 6:48, 7:26, 9:1, 11:8} |
| 11 | {1:496, 2:98, 3:100, 5:164, 6:1, 8:100, 10:64} | {1:496, 2:66, 3:32, 4:100, 6:164, 7:1, 9:100, 11:64} |

- **P-K2 HELD:** the breathless group is never K, 2K or K-bar. The 2 of the seam is **not** the fold law's «every clock doubled».
- **What the breath is (MEASURED, 5/5):** removing it multiplies every «big clock» by `2^{v_2(m) - v_2(m+1)}` and leaves the small clocks (the handrail factors) alone: shift -1 at n = 3, +1 at n = 5, -2 at n = 7, +2 at n = 9, -1 at n = 11, i.e. exactly `v_2(m) - v_2(m+1)` with m = (n-1)/2. READING: each Weyl staircase passes once through floor m + 1, and its big clock carries the product of the diagonals it passes; the breath is one factor `2(m+1)` against `2m` in each big clock.

**K3, coming closer and closer — MEASURED, n = 2..12.** Replace the kiss matrix by its residues modulo 2^N (a mirror that agrees with the true weld modulo 2^N on the landing block):

| n | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| e_max (largest exponent of K) | 2 | 3 | 5 | 6 | 6 | 7 | 10 | 11 | 11 | 11 | 13 |
| **N_lock** (from N_lock on, the group is exactly K ⊕ Z) | 2 | 1 | 2 | 2 | 3 | 2 | 2 | 2 | 3 | 2 | 3 |

- **The weld needs only two or three binary digits of the kiss**: G mod 4 (or mod 8 for n = 6, 10, 12) already gives the whole group, while the group itself has exponents up to 13. With G mod 2 (N = 1) the group is wrong for every n except 3.
- My sealed P-K3 («N_lock < e_max and N_lock <= floor(log_2 n) + 2») **FAILED at n = 2** (N_lock = e_max = 2) and held for n = 3..12. The guess «grows like log_2 n» is not supported: N_lock stays at 2–3. Explaining why 3 binary digits suffice is open (C.3); a READING: the high powers of 2 are carried by the staircases (the diagonals 2k), and the kiss only has to say **which** staircases are welded, which is decided modulo 8.

## 4. LEG D — the whole 2-part — STATUS: NOT CONCLUDED (stated in closed form as a CONJECTURE, D.5, that survives every sealed test to n = 40 and every proved theorem to n = 128; the reduction is proved, the rule inside each tilting module is not)

### D.1 What is stated, and with which grade

- **PROVED modulo standard tilting theory (Theorem RT, C.1):** `Syl_2 K(Q_n) ⊕ Z_2 ≅ ⊕_lambda X(lambda, (n-lambda)/2)^{m_lambda(n)}`, with `m_lambda(n)` given by characters (exact, finite) and each `X(lambda, i)` the cokernel of an explicit operator on an explicit small lattice. This is an exact rule for every n, but `X(lambda, i)` is not yet in closed form (C.3).
- **MEASURED:** the cells n = 2..32 (`logs/legD_tilt_32.log`) and n = 33..40 (`logs/legD_oos_2.log`); n = 14 confirmed directly (P-RT4).

### D.2 The sealed prediction of n = 12, 13

The cells n = 12, 13 were predicted by the tilting route from small models before comparison (P-RT2, sealed in S1) and agree with `RETOS_AL_ALCANCE_v1.md`. n = 14 was sealed (S4) and confirmed by a direct computation.

### D.3 Against the literature and against the proved layers (`logs/legD_checks_32b.log`, 65/65)

| check | source | grade of the source | result on the tilting cells |
|---|---|---|---|
| top factor `v_2 c_1 = max(max_{x<n}(v_2 x + x), v_2 n + n - 1)` | Gao et al. Thm 4.1 | proved | 31/31 (n = 2..32) |
| 2nd..(n-1)th factors `= max_{x<n}(v_2 x + x)` | Gao et al. Thm 4.2 | proved | 31/31 |
| n-th factor `= max(max_{x<n-1}(v_2 x + x), v_2(n-1) + n - 3)` | Gao et al. Conj 4.14 (data n <= 11) | conjecture | **holds n = 3..32** |
| (n+1)-th factor `= max_{x<n-1}(v_2 x + x)` | JMM poster 2019 (n >= 4) | conjecture | **holds n = 4..32** |
| `Syl_2 K(Q_{2^k}) = Syl_2 K(Q_{2^k - 1})^2 x Z/2^{2^k + k - 1}` | Gao et al. Conj 5.4 | conjecture | **holds k = 2, 3, 4, 5** (n = 4, 8, 16, 32) |
| number of Z/2 factors `a_n = 2^{n-2} - 2^{floor((n-2)/2)}` (layer 1) | pencil note §1.4 | proved | 30/30 (n = 3..32) |
| number of Z/4 factors and of factors of order >= 8 (Corollary A) | pencil note Thm 6.3 | proved (two readings) | 30/30 |
| number of factors `2^{n-1} - 1` | Bai | proved | 31/31 |

These are MEASURED agreements of the tilting cells with statements proved elsewhere (a strong check of Theorem RT and of my engine) and with three published conjectures, now supported to n = 32 instead of n <= 11.

### D.4 The fold law, through the tilting route (sealed S6; `logs/legD_fold_32.log`)

**Dictionary (PROVED, gated).** The antipode a = x_1...x_n acts on V^(x)n as `g^(x)n` with `g = [[1,0],[-1,-1]] ∈ GL_2(Z)` (`g b0 = b0 - b1`, `g b1 = -b1`; gate: equal to multiplication by a in the basis s_S, n = 1..6). The tilting decomposition holds for GL_2 (V^(x)n is a polynomial GL_2-module), the summand of highest weight lambda being `T(lambda) (x) det^{(n-lambda)/2}`, on which a acts as `(-1)^{(n-lambda)/2} g`. Hence, exactly as Theorem RT:

  `K-bar(Q_n) ⊕ Z_2 ≅ ⊕_lambda Xbar(lambda, (n-lambda)/2)^{m_lambda(n)}`,   `Xbar(lambda, i) := coker[ sigma_c | (-1)^i g - 1 ]` on `T_{Z_2}(lambda)`, c = lambda + 2i.

On a Steinberg lattice `St_k = Gamma^{2^k - 1}(V)` (divided powers) g acts by `g e_s = sum_u (-1)^{u+s} C(u+s, s) e_{u+s}`.

- **P-F1 HELD, 11/11:** the folded cube from small models equals the direct K-bar, n = 3..13.
- **P-F2 HELD, 30/30: the fold law `2K(Q_n) ≅ K-bar(Q_n)` on 2-parts holds for every n = 3..32** (MEASURED; previously n <= 13).
- **P-F3 FAILED as sealed, but only at lambda = 0; HELD for every lambda = 1..31** (all cells lambda + 2i <= 32): **`Xbar(lambda, i) = 2·X(lambda, i)` family by family.** At lambda = 0 (the trivial module, `Xbar(0, i) = X(0, i)`) it fails, and lambda = 0 never occurs in V^(x)n for n >= 1 (`logs/legD_fold_detail.log`; for even n the trivial Weyl factors are welded into T(2)-type modules).

**What this gives (READING with a PROVED reduction).** By the two decompositions, **the fold law for every n is equivalent to the family-by-family statement `Xbar(lambda, i) ≅ 2 X(lambda, i)` for every lambda >= 1 occurring in some V^(x)n and every i** — one statement per indecomposable tilting module, independent of n. It is MEASURED for lambda <= 31. In Rafa's words: the cube and the folded cube take turns (se van turnando) inside each rivet separately.

### D.5 The whole 2-part of K(Q_n), every n — CONJECTURE (closed form)

**Conjecture W.** For every n >= 1,

  `Syl_2 K(Q_n) ⊕ Z_2  ≅  ⊕_lambda [ ⊕_{a=1}^{k-1} (Z/2^a)^{2^{|I|+k-1-a}}  ⊕  H(lambda, (n-lambda)/2) ]^{m_lambda(n)}`,

where, for each lambda ≡ n (mod 2):
- `lambda + 1 = 2^k + sum_{t in I} 2^t` (k the leading binary digit, I the other digits);
- `H(lambda, i)` is the multiset of 2^{|I|} big clocks given by Conjecture H (C.4): naive clocks `B(mu, j) = (mu+1) + v_2((j+mu)!/(j-1)!) - v_2(mu!)` of the Weyl staircases `mu + 1 = 2^k ± 2^t (t ∈ I)` at shifts `j = i + (lambda - mu)/2`, plus the transfers `sum (next(t) - t)` over the minus signs, pooled (adjacent violators, ordered by mu) into a non-increasing sequence; one Z when i = 0;
- `m_lambda(n)` is given by the **fusion recursion** (PROVED from Donkin's tensor product theorem: `V (x) T(odd lambda) = T(lambda+1)`, `V (x) T(0) = T(1)`, `V (x) T(2 l + 2) = T(2 l + 1)^2 ⊕ Frob(V (x) T(l))` with `Frob T(nu) = T(2 nu + 1)`), starting from `m(1) = T(1)`; it agrees with character peeling for n = 1..64 (`logs/legD_fusion.log`).

No Smith form is needed: the right-hand side is a finite computation with binomial valuations (`engines/rule.py`; n = 128 in a fraction of a second).

**What is proved and what is not.** PROVED: the reduction to tilting modules (Theorem RT, modulo cited tilting theory), the multiplicities, the first layer of the shape (rank of F mod 2), the Steinberg families (Theorem S), lambda = 2 (C.6). CONJECTURE: the small clocks of non-Steinberg families (P-X1) and the big clocks (Conjecture H). **Evidence:** 1271/1271 cells of X(lambda, i) (lambda <= 31, i <= 40); n = 2..40 exactly (n <= 14 also by direct Smith forms), with **n = 33..40 sealed before computation**; 294/294 cells of 42 large models (every tilting module up to highest weight 63); no violation of any proved theorem (Bai, Gao 4.1, 4.2, the pencil note's layers) for n <= 128; Gao et al.'s Conjectures 4.14 and 5.4 and the poster's (n+1)-th factor hold for n <= 128 under it.

**Small table from the closed rule** (exponent:multiplicity; n = 14..16 also by the tilting route and n = 14 directly):

| n | Syl_2 K(Q_n) |
|---|---|
| 14 | {1:4032, 2:792, 3:364, 4:1, 6:64, 7:1848, 8:26, 9:64, 10:364, 11:546, 13:64, 14:26} |
| 15 | {1:8128, 2:1820, 3:1, 5:128, 6:1288, 7:1926, 8:1378, 9:14, 10:336, 11:910, 12:336, 13:14, 14:90, 15:14} |
| 16 | {1:16256, 2:3640, 3:2, 5:256, 6:2576, 7:3852, 8:2756, 9:28, 10:672, 11:1820, 12:672, 13:28, 14:180, 15:28, 19:1} |

## 5. LEG E — the metaphor — STATUS: CLOSED

**Two lines.** The image that fits is **the rivet**: each indecomposable tilting module T(λ) is a staircase from the ground (Weyl, handrail 1, 2, 3, …) and a staircase from the roof (dual Weyl, …, 3, 2, 1) riveted at the landing, and the cube is a pile of such rivets; the mirror does not weld by being applied, it welds by being the thing that the riveted piece is symmetric under. **It helped**: the reading «look for the pieces that the mirror leaves fixed», sealed before any number (S0), led directly to Theorem RT and to every new cell of this flight.

Image by image (which served, which was decorative):

| image | verdict | what it became |
|---|---|---|
| 7, the hall of mirrors | **served, in a changed reading** | the auditor's reading (apply each mirror, glue) gave the catalogue, Theorem L (the kiss matrix) and K1–K3; my reading (the welds are the mirror's fixed pieces) gave Theorem RT |
| 7, the kiss | **served** | K1 is exact (Theorem L: the whole landing lives on the middle floor); K3 gave a number (the kiss is needed only mod 4 or 8); K2 measured what the breath does (rescales every big clock by `2^{v_2(m) − v_2(m+1)}`) — and that it is **not** the fold law |
| 2, sea or drops | **served** | the drops are the tilting families λ, with groups X(λ, i) independent of n |
| 4, binary | **served** | inside each family every binary layer halves: dim/2^a factors of exponent ≥ a (P-X1) |
| 3, se van turnando | **served** | the fold law holds to n = 32 and **family by family** (Xbar = 2X for every λ ≥ 1) |
| 6, the carry is the height | **served** | a big clock is «what the rooms pay (diagonal 2k) over what the handrail carries»; its excess over 2^k + k is a Kummer carry v_2(q) |
| 1, a prize for each cube | **served, loosely** | each staircase (Weyl factor) of a rivet gets exactly one big clock: 2^{|I|} prizes per T(λ) |
| 5, the wound | **decorative in this flight** | not used |

## 6. Sealed predictions, and how each one ended

All in `checks/SEALED.md`, each written with its time before the measurement.

| id | prediction | ended |
|---|---|---|
| S0 | translation of the images; my reading R-T (welds = tilting modules) | used; R-T confirmed (S1) |
| P-RT1 | two models give the same X(λ, i) | **held** 127/127 |
| P-RT2 | the cube n = 2..13 from small models | **held** 12/12 |
| P-RT3 | Steinberg families = full Weyl staircase | **held** |
| P-RT4 | n = 14 from tilting = direct | **held** |
| P-M1, M2, M4, M5 | catalogue identities and controls | **held** |
| P-M3 | <c, t> infinite (against the auditor's «small group») | **held** |
| P-L1 | landing formulas exact | **held** |
| **P-L2** | no naive weld works for n ≥ 2 | **FAILED at n = 3** (there V^(x)3 = T(3) ⊕ T(1)^2, nothing to weld) |
| P-K1 | the landing is read on the middle floor | **held** (by construction) |
| P-K2 | breathless group ≠ K, 2K, K-bar | **held** 5/5 |
| **P-K3** | N_lock < e_max and ≤ ⌊log_2 n⌋ + 2 | **FAILED at n = 2** (N_lock = e_max = 2); held n = 3..12; «grows like log n» not supported |
| P-X1 | small clocks + 2^{|I|} big clocks | **held** 1312/1312 |
| P-X2 | Steinberg big clock 2^k + k + v_2(q) | **held** |
| **P-X3** | sum rule for the big clocks | **FAILED at i = 0** (31 cells; determinant 0, kernel correction missing); held i ≥ 1 |
| P-F1 | folded cube from small models | **held** 11/11 |
| P-F2 | fold law n = 3..32 | **held** 30/30 |
| **P-F3** | Xbar = 2X family by family | **FAILED at λ = 0 only** (16 cells; λ = 0 never occurs in the cube); held for every λ = 1..31 |
| **P-H1** | labelled Frobenius shift of the big clocks | **FAILED** 91/615 cells (where clocks pool) |
| P-H2 | two-clock rule (|I| = 1) | **held** 410/410 |
| P-H3 | general big-clock rule (Conjecture H) | **held** 1271/1271 (after fixing error E3 in my test code) |
| P-H4 | n = 33..40 from the rule, sealed before computation | **held** 8/8 |
| P-H5 | 42 large models, highest weight 32..63 | **held** 294/294 |
| P-H6 | rule vs proved theorems, n ≤ 128 | **held** |
| P-H7 | rule vs Conj 4.14, poster, Conj 5.4, n ≤ 128 | **held** |
| P-R1 | Frobenius odd step with doubled payment | **held** 276/276 (after fixing error E4 in my test code) |

## 7. Runs: estimate, log, peak memory, time

| run | estimate written before | log | result (peak, time) |
|---|---|---|---|
| legA_1 (`engines/legA.py 11`: A0 engine vs flint n=2..6, A1 cube n=2..11 full ring + halving, A3 fold law n=3..11) | 30 s, 300 MB | `logs/legA_1.log` | **KILLED by the watchdog, memory, 1.27 GB at 42 s**, inside flint `snf()` on the singular 64x64 matrix of sigma (n = 6). Error E1 (§8). |
| legA_2 (same script, flint on the reduced Laplacian) | 30 s, 300 MB | `logs/legA_2.log` | VIGIA-FIN-OK, 25 MB, 0.3 s (the C elimination is fast because sigma is sparse and level-triangular) |
| legA2_1 (`engines/legA2.py 11`: K/F_t vs chains, n = 2..11, all t) | 20 s, 100 MB (Python loops build the truncations) | `logs/legA2_1.log` | VIGIA-FIN-OK, 198 MB, 0.4 s |
| legA3_1 (`engines/legA3.py`: cube and folded cube at n = 12, 13 by halving) | 60 s, 600 MB (4096x4096 int64 = 134 MB, plus copies; f needs 4096 np.add.at passes) | `logs/legA3_1.log` | VIGIA-FIN-OK, 590 MB, 5 s |
| legB_1 (`engines/legB.py 11`: Theorem Z dets n = 1..11 all floors with flint, controls C1-C3) | 60 s, 300 MB (largest matrix 462x462) | `logs/legB_1.log` | VIGIA-FIN-OK, 43 MB, 1.2 s, 15 PASS |
| legD_tilt_32 (`engines/legD_tilt.py 32`: X(lambda,i), lambda+2i <= 32, greedy Steinberg models; cube n = 2..32) | 60 s, 300 MB (largest model 2048x2048, lambda = 27, 28) | `logs/legD_tilt_32.log` | VIGIA-FIN-OK, 152 MB, 0.5 s |
| legD_checks_32 (`engines/legD_checks.py 32`: cells n=2..32 vs Gao et al. Thm 4.1, 4.2, Conj 4.14, poster (n+1)-th, Conj 5.4, pencil note layers 1-2) | 2 s, 50 MB (reads the JSON) | `logs/legD_checks_32.log` | **KILLED by the watchdog, memory, 1.39 GB at 1 s**: I expanded the multiplicities into a list of 2^31 exponents (n = 32). Error E2. |
| legD_checks_32b (same, working with multiplicities) | 2 s, 50 MB | `logs/legD_checks_32b.log` | VIGIA-FIN-OK, 7 MB, 0 s, 65 PASS |
| legF_cat (`engines/legF.py cat 8`: catalogue gates n = 1..8) | 20 s, 200 MB (256x256 dense products; antipode by np.add.at) | `logs/legF_cat.log` | VIGIA-FIN-OK, 25 MB, 0.1 s, 53 PASS |
| legF_rest (`engines/legF.py cand/floors/kiss 12`: candidates n = 2..12, truncations n = 2..11, breathless n odd, K3 lock n = 2..12) | 5 min, 700 MB (K3: about e_max + 3 Smith forms of the 4096 matrix at n = 12; S_formula built by Python loops) | `logs/legF_cand.log`, `logs/legF_floors.log`, `logs/legF_kiss.log` | VIGIA-FIN-OK x3: 218 MB 2 s; 706 MB 2 s; 577 MB 34 s |
| legC_mult (`engines/legC_mult.py 16`: m_lambda(n) against d_j) | 1 s, 20 MB | `logs/legC_mult.log` | VIGIA-FIN-OK |
| legC_X_31 (`engines/legC_X.py 31 40`: X(lambda,i), lambda <= 31, i <= 40 + (31-lambda)/2; tests P-X1..3) | 3 min, 300 MB (models up to 2048, about 40 shifts each for the big ones) | `logs/legC_X_31.log` | VIGIA-FIN-OK, 152 MB, 6.3 s |
| legF_land (`engines/legF.py land 12`: exact change of basis n = 2..11 with flint inverses; coker S(G) n = 2..12; kiss matrix dets) | 90 s, 700 MB (n = 12: 4096^2 int64 = 134 MB plus copies; flint det of 924x924) | `logs/legF_land.log` | VIGIA-FIN-OK, 640 MB, 18 s, 32 PASS |
| legD_fold_32 (`engines/legD_fold.py 32`: Xbar table and X table to N = 32, P-F1..F3) | 60 s, 400 MB (rectangular d x 2d Smith forms, d <= 2048) | `logs/legD_fold_32.log` | VIGIA-FIN-OK, 453 MB, 10 s |
| legD_fold_detail (list of the P-F3 failures) | 1 s | `logs/legD_fold_detail.log` | VIGIA-FIN-OK |
| legD_oos (`engines/legD_oos.py`: rule vs tilting n = 2..40; big models lambda 32..63, dim <= 4096, shifts 0..6) | 5 min, 600 MB (models up to 4096 x 4096 int64 = 134 MB, about 7 shifts each, maybe 40 models) | `logs/legD_oos.log` (first run) | P-H4 done (8/8 PASS); then stopped by my engine's own guard: an exponent 62 >= 64 - 4 in a big model (exponents ~ lambda + 1 for lambda ~ 63). Not a watchdog kill. |
| legD_oos_2 (same, 128-bit words) | 10 min, 900 MB (u128 doubles the matrix memory: 4096^2 x 16 B = 268 MB) | `logs/legD_oos_2.log` | VIGIA-FIN-OK, 903 MB, 36 s, 11 PASS |
| legD_far_128 (`engines/legD_far.py 128`: the closed rule against proved theorems and conjectures, n = 2..128) | 2 min, 100 MB (characters of degree <= 128, 2^|I| <= 64 sign patterns) | `logs/legD_far_128.log` | VIGIA-FIN-OK, 23 MB, 0.4 s |
| analysis runs of the big clocks: `legC_H_I1`, `legC_H2`, `legC_frob` (P-H1), `legC_H1rule` (P-H2), `legC_Hrule` (P-H3; buggy first run kept as `legC_Hrule_BUGGY_E3.log`), `rule_33_40` (sealed values), `legC_frob2` (P-R1; buggy first run kept as `legC_frob2_BUGGY_E4.log`, and one run stopped by my engine's guard at alpha = 8, exponent 124), `legD_fusion` | each under 2 s and 250 MB (estimates: seconds, < 300 MB) | `logs/<name>.log` | all VIGIA-FIN-OK |
| legC_halfsum (`engines/legC_halfsum.py`: per-summand halving gate, odd nu <= 29) | **written late (E6)**: 5–10 min, 800 MB (dense tau(tau+2) on models up to 2048, 128-bit Smith) | `logs/legC_halfsum.log` | VIGIA-FIN-OK, 279 MB, 131 s, 117/117 |
| legA14_1 (`engines/legA14.py 13`: direct Smith of theta on Z[(Z/2)^13], uint32 in place) | 60 s, 500 MB (8192^2 x 4 B = 268 MB + build temporaries) | `logs/legA14_1.log` | VIGIA-FIN-OK, 284 MB, 10 s |
| legC_rt_1 (`engines/legC_rt.py 12`: tilting gates RT0-RT3, route V up to V^(x)12 with shifts, route S, cube n=2..13 from small models) | 120 s, 400 MB (largest matrices 4096x4096 for V^(x)12, ~10 shifts; models up to 2^9) | `logs/legC_rt_1.log` | VIGIA-FIN-OK, 541 MB, 5.7 s, 6 PASS |

## 8. Errors of my own

- **E1 (09:14).** I used flint `fmpz_mat.snf()` as the independent route on the *singular* 64x64 matrix of sigma at n = 6, after the mission warned that flint's SNF had blown 1.2 GB on a 64x128 matrix. Estimate 300 MB; the watchdog killed it at 1.27 GB. Fix: the independent route is now flint SNF on the **reduced Laplacian in the vertex basis** (delete the sink row and column; non-singular), n <= 6, which is also a genuinely different matrix from sigma in the basis s_S.
- **E2 (09:36).** In the Leg D checks I expanded each cell into the list of its exponents with repetition (2^31 entries at n = 32); estimate 50 MB, killed at 1.39 GB after 1 s. Fix: the k-th largest factor is read from the multiplicities.
- **E3 (09:55).** In the first test of P-H3 my script added next(t) instead of next(t) − t (the sealed rule says the latter); 902 false failures. The buggy log is kept as `logs/legC_Hrule_BUGGY_E3.log`; the rule was not changed, only the code, and the test was re-run.
- **E4 (10:01).** In the first test of P-R1 my code raised only the non-zero exponents of X^(2alpha) by one and forgot that its unit factors become Z/2 (the sealed statement says «every exponent»); 245 false failures. Buggy log kept as `logs/legC_frob2_BUGGY_E4.log`; code fixed, prediction unchanged, test re-run.
- **E5 (10:00).** The run of `legC_frob2` that my engine stopped at alpha = 8 (exponent 124 >= 128 - 4) wrote to `logs/legC_frob2.log`, and the next run of the same name overwrote it; its content survives only in this report (§7). A slip of the disk rule.
- **E6 (10:05).** I launched `legC_halfsum` (per-summand halving gate) **without writing its estimate first**; it ran past two minutes (dense products and 128-bit Smith forms of 2048 x 2048 matrices). Estimate written afterwards in §7, marked as late.
- **E7 (diary).** Several short analysis runs (`legC_mult`, `legC_H_I1`, `legC_H2`, `legC_frob`, `legC_H1rule`, `rule_33_40`, `legC_frob2`, `legD_fusion`) have a line in `logs/DIARY.md` only after the step, not before it, as the disk rule asks; their logs carry the VIGIA line with the time taken.

## 9. What I did not do

- **No proof of the closed rule** (Conjecture H / W) beyond the Steinberg families and λ = 2: the shape P-X1 and the big-clock rule are measured, not proved. The reduction (Theorem RT) is proved modulo cited tilting theory.
- **Theorem RT rests on citations** (lifting of tilting modules to Z_2, Jantzen RAGS II.E): I did not re-prove them.
- **Novelty not checked.** Bai (2003) not read; the literature on tilting modules of SL_2 in characteristic 2 (multiplicities of T(λ) in V^(x)n, e.g. recent work on «fractal» tensor powers) was not read — I used no web access; the use of tilting modules for sandpile groups may exist.
- K3 not run at n = 13 (the int64 matrix of S(G) would pass the memory cap); the reason why the kiss is needed only mod 4 or 8 is not explained.
- **The even Frobenius step** (T(2λ₁+2) = T(2) ⊗ T(λ₁)^[1] for the operator σ^(α)) was not formulated; with P-R1 (odd step, measured) it is the natural route to a proof of Conjecture W.
- Routes of the mission not used: Leg C.4 (the Chaise's Theorem C at q = 2 for the middle Specht piece) — the landing modulo 2 came out directly as the rank of F (half of every tilting module), so the Specht bound was not needed; Leg C.3 (the fold law as the weld) became D.4 (the fold law family by family), not a proof of the weld.
- Theorem RT's citations (Jantzen RAGS II.E) were not re-proved; an elementary proof for V^(x)n (idempotents of the image of Z_2[S_n]) is owed.
- No Lean.
