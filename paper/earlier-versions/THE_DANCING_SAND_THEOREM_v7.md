# THE DANCING SAND THEOREM
## The 2-part of the sandpile group of the hypercube, for every n

**Rafael Amichis Luengo**

Madrid, Spain · tretoef@gmail.com · 6 October 2026 · version 7

---
## Abstract

Let `K(Q_n)` be the sandpile group (critical group, Jacobian) of the `n`-dimensional hypercube graph `Q_n`. Its odd part was determined by Bai in 2003; its `2`-part has been open since then, and the latest work on it determines its `n − 1` largest cyclic factors. **We determine the whole 2-part of `K(Q_n)` for every `n`, by an explicit rule.** The group splits over the indecomposable tilting modules `T(λ)` of `SL_2` in characteristic `2` that occur in `V^{⊗n}`, with their multiplicities. The contribution of `T(λ)` at the shift `i = (n − λ)/2` consists of explicit small cyclic factors and of `2^{|I|}` large ones, where `I` is the set of binary digits of `λ + 1` below the leading one. The large ones are obtained by pooling a sequence of explicit integers — binomial valuations and carries — into a non-increasing sequence, in the manner of isotonic regression. The proof reduces each contribution, by elimination inside explicit `2`-adic lattices, to the Smith form of an explicit `2^{|I|} × 2^{|I|}` integer matrix, and computes that Smith form from the valuations of its entries. It needs a unique cheapest matching for an upper bound and an inductive potential for a lower bound. As consequences we recover Bai's counts and the theorems of Gao, Marx-Kuo, McDonald and Yuen on the largest factors, and we prove their Conjectures 4.14 and 5.4 and the formula for the `(n+1)`-th factor stated in the 2019 poster of three of them. **We also prove the fold law: the 2-part of the sandpile group of the folded cube `Q_n/⟨(1,…,1)⟩` is `2·Syl_2 K(Q_n)`**, the group obtained by lowering every exponent by one. With the results above this gives the whole `2`-part of the sandpile group of the folded cube, and, with the known odd part, its whole sandpile group. This work has not been refereed by a human expert.

---

## 1. Introduction and main results

### 1.0 Summary of results

For `n ≥ 1`, `K(Q_n)` is the sandpile group of the `n`-cube, `K̄(n)` that of the folded `n`-cube `Q_n/⟨𝟙⟩` (§1.3), and `ℤ_2` is the ring of `2`-adic integers.

| Result | What it says | Where |
|---|---|---|
| **Main Theorem** (the Dancing Sand Theorem) | `Syl_2 K(Q_n) ⊕ ℤ_2 ≅ ⊕_λ X(λ, (n−λ)/2)^{m_λ(n)}`, with `X(λ, i)` given by an explicit rule | §1.2, proof in §8 |
| **Theorem D** | each `X(λ, i)` is a known group of small clocks plus `coker(2^k M(λ, i))`, `M` an explicit `2^{|I|} × 2^{|I|}` matrix with closed-form entries | §4 |
| **Theorems O and F** | the Smith form of `M(λ, i)` is the pooled sequence of clocks: an upper bound through a unique cheapest matching, a lower bound through a potential built digit by digit | §6, §7 |
| **Theorem DW** (the fold law, «dry and wet») | `Syl_2 K̄(n) ≅ 2·Syl_2 K(Q_n)`; equivalently `Syl_2 K(Q_n) ≅ (ℤ/2)^{a_n} ⊕ (Syl_2 K̄(n) with every exponent raised by one)`, `a_n = 2^{n−2} − 2^{⌊(n−2)/2⌋}` | §1.3, proof in §10 |
| **Corollary 1.4** | the whole sandpile group of the folded cube | §1.3, §10.8 |
| **Corollary 1.5** | Bai's two counts, re-proved from the rule | §9.1 |
| **Corollary 1.6** | the `n + 1` largest cyclic factors of `Syl_2 K(Q_n)`: Gao et al.'s Theorems 4.1 and 4.2, their Conjecture 4.14 and the `(n+1)`-th factor of the 2019 poster [MGM19] | §9.2 |
| **Corollary 1.7** | `Syl_2 K(Q_{2^e}) ≅ Syl_2 K(Q_{2^e−1})^2 ⊕ ℤ/2^{2^e+e−1}` (Gao et al.'s Conjecture 5.4) | §9.3 |

Every proof behind the table was re-derived by a reader other than its author. The chains of the Main Theorem and of Theorem DW were read cold before this text was written, by readers with no access to the audits. Version 1 of this text was read cold as a whole on 5 October 2026 by a reader with no access to the constructors' reports, the audits or the earlier readings: «holds with gaps». It found one gap: the integer part of Lemma 7.2(b) was false as stated, and four proofs used it; no theorem was affected. Version 2 repaired it (§7.1, §7.4, §7.5, §9.2), and the changes of version 2 were read cold the same day by a fourth reader: **the repair holds**. That reader found one false sentence, in a remark used nowhere (the author then found the same missing hypothesis in Lemma 10.6(a), harmless because its only use is for an even system), two rows of §12.1 that said more than their code, and points of presentation; it also found, with a two-line proof, that the fit of every house is integral (Lemma 7.9). The changes of version 3 were read cold by a fifth reader: **they hold**, with no gap and no error; that reader found points of presentation and defects of typesetting, corrected in version 4 except two (Appendix A). The changes of version 4 were read cold by a sixth reader: the mathematics of every change **holds**, with no gap and no error; that reader found one false number and one false sentence in the record of the readings, inexact sentences, and defects of typesetting, corrected in version 5. The changes of version 5 were read cold by a seventh reader: the mathematics of every change **holds**, with no gap and no error; that reader found one false sentence in the record of the readings, inexact sentences, and defects of typesetting, corrected in version 6. The changes of version 6, and its whole pdf page by page, were read cold by an eighth reader: the mathematics of every change **holds**, and nothing on the page is broken; that reader found two false sentences in the record of the work, one row of §12.2 that printed only one of the two ranges its reader ran, and one sentence of §1.7 that could be misread, corrected in this version 7. **The changes of version 7 have not yet been read cold** (§13, Appendix A). No human expert has refereed this work. The words of our own are translated into standard terms in §1.7; what we found in the literature, and where we searched, is in §1.8.

### 1.1 The problem

For a finite connected graph `G` with Laplacian `L(G)`, the cokernel of `L(G)` acting on `ℤ^{V(G)}` is `ℤ ⊕ K(G)`, where `K(G)` is a finite abelian group of order the number of spanning trees of `G` (Kirchhoff). It is called the sandpile group, the critical group or the Jacobian of `G`; see [Lor91], [Big99], [Kli18]. For the hypercube `Q_n` — vertices `{0,1}^n`, edges between words that differ in one letter — the number of spanning trees is `2^{2^n − n − 1} ∏_{j=1}^{n} j^{C(n,j)}`, so `K(Q_n)` has order a power of `2` times `∏ j^{C(n,j)}`.

Reiner conjectured in 2001 the number of cyclic factors of `K(Q_n)` and the number of its factors `ℤ/2`, and Bai proved both and determined every odd Sylow subgroup [Bai03]: for an odd prime `p`, `Syl_p K(Q_n) ≅ Syl_p ⊕_{j=1}^{n} (ℤ/j)^{C(n,j)}` [Bai03, Theorem 1.2]. About the `2`-part he wrote: «The full structure of the Sylow-2 subgroup of the critical group of the `n`-cube is still unknown» [Bai03, p. 253]. The question was repeated by Ducey and Jalil [DJ14] («the full structure of the 2-primary component of both the critical group and the Smith group of the `n`-cube remain unknown»). Chandler, Sin and Xiang computed the Smith group of the adjacency matrix of `Q_n` and wrote about the critical group: «only the 2-Sylow subgroup of the critical group remains to be determined, for both odd and even `n`. We do not have any conjecture about its exact structure» [CSX17, §5.2]. Iga, Klivans, Kostiuk and Yuen observed that for Cayley graphs of `𝔽_2^r` «the 2-Sylow subgroup of their critical groups, or even the just [sic] 2-rank of the Laplacians, has been rather difficult to understand» [IKKY23, §7]. Gao, Marx-Kuo, McDonald and Yuen determined the largest cyclic factor and the next `n − 2` [GMMY24, Theorems 4.1, 4.2], conjectured the `n`-th [GMMY24, Conjecture 4.14] and a doubling relation between the cubes of dimension `2^k − 1` and `2^k` [GMMY24, Conjecture 5.4], and wrote that «determining the complete structure still seems out of reach at this moment». The `(n+1)`-th factor was conjectured on the 2019 poster of Marx-Kuo, Gao and McDonald, which says that «the Sylow-2 subgroup remains a mystery» [MGM19].

This paper determines the whole `2`-part, for every `n`.

### 1.2 The main theorem

We write `Syl_2 A` for the `2`-primary part of a finite abelian group `A`, and we describe `2`-groups by their exponents: `{e_1: c_1, e_2: c_2, …}` means `⊕ (ℤ/2^{e_j})^{c_j}`. As usual, `ℤ_2` is the ring of `2`-adic integers, `s_2(x)` the number of ones in the binary expansion of `x ≥ 0`, `v_2` the `2`-adic valuation, and
- `κ(a, b) := s_2(a) + s_2(b) − s_2(a + b)`, the number of carries in the binary addition `a + b` (`a, b ≥ 0`); by Kummer's theorem `κ(a, b) = v_2 C(a + b, a)`;
- `φ(x) := x + v_2(x)` for `x ≥ 1`.

**Families.** For an integer `λ ≥ 0` write
  `λ + 1 = 2^k + Σ_{t∈I} 2^t`,  `I ⊆ {0, 1, …, k − 1}`,
so `k` is the leading binary digit of `λ + 1` and `I` the set of the others. For `t ∈ I` put
  `next(t) := min{u ∈ I ∪ {k} : u > t}`  and  `h_t := next(t) − t`.
The subsets `D ⊆ I` are the **dancers** of the family; for a dancer put `o_D := Σ_{t∈D} 2^t` and `h(D) := Σ_{t∈D} h_t`. The **o-order** lists the dancers by increasing `o_D`, from `∅` to `I`.

**Multiplicities.** Let `m_λ(n)` be the integers defined by
  `Σ_λ m_λ(0)[λ] = [0]`,  `Σ_λ m_λ(n)[λ] = V·Σ_λ m_λ(n−1)[λ]`,
where `V·` is the additive operator on formal sums of symbols `[λ]` given by
  `V·[0] = [1]`,  `V·[2l + 1] = [2l + 2]`,  `V·[2l + 2] = 2[2l + 1] + Φ(V·[l])`,  `Φ([ν]) := [2ν + 1]`.
(The recursion is well founded: `V·[2l+2]` calls `V·[l]` with `l < 2l + 2`.) By Theorem 3.6, `m_λ(n)` is the multiplicity of the indecomposable tilting module `T(λ)` of `SL_2` in characteristic `2` in the tensor power `V^{⊗n}` of the natural module. Only `λ ≡ n (mod 2)` with `1 ≤ λ ≤ n` occur for `n ≥ 1`, and `m_n(n) = 1`.

**Clocks.** Fix a family `λ` and a shift `i ≥ 0`. For a dancer `D` with `(i, D) ≠ (0, ∅)` put `ξ_D := λ + 1 − 2o_D` (a positive integer) and
  **`u_i(D) := φ(ξ_D) + κ(i + o_D − 1, ξ_D) + h(D)`,**
and put `u_0(∅) := ∞`. These are the **raw clocks** of the family at shift `i`.

**Pooling.** For a finite sequence of integers `x_0, …, x_{N−1}`, its **integer antitonic fit** is obtained as follows. Partition the positions into consecutive blocks by the pool-adjacent-violators algorithm, so that the block means are strictly decreasing (adjacent blocks with equal means are merged) and each block value is the mean of its entries: this is the antitonic least-squares fit [ABERS55], [BBBB72]. Then replace a block of `p` positions with sum `S` by `S mod p` copies of `⌈S/p⌉` followed by `p − (S mod p)` copies of `⌊S/p⌋`. In the cube the rounding never acts: every block mean of the raw clocks is an integer (Lemma 7.9, with Proposition 5.3, Lemma 7.5 and Proposition 5.4; see §8), so `ŷ_i` below is the antitonic least-squares fit itself, a non-increasing sequence of integers. The rounding is kept in the definition only so that the rule is defined for every sequence of integers. At shift `0` the entry `∞` stands first and is not pooled with anything.

**The group of a family.** Let `ŷ_i(D)` be the integer antitonic fit of the raw clocks `u_i(D)`, read in o-order. Put
  **`X(λ, i) := ⊕_{a=1}^{k−1} (ℤ/2^a)^{2^{|I| + k − 1 − a}} ⊕ ⊕_{D ⊆ I} ℤ/2^{ŷ_i(D)}`,**
with `ℤ/2^∞ := ℤ_2`. The first sum is the family's **small clocks**, the second its `2^{|I|}` **big clocks**.

> **Main Theorem (the Dancing Sand Theorem).** For every `n ≥ 1`, as `ℤ_2`-modules,
>   **`Syl_2 K(Q_n) ⊕ ℤ_2 ≅ ⊕_{1 ≤ λ ≤ n, λ ≡ n (mod 2)} X(λ, (n − λ)/2)^{m_λ(n)}`.**
> The free summand is the big clock `ŷ_0(∅) = ∞` of the family `λ = n`.

The right-hand side is a finite computation with binomial valuations; no Smith form is needed (`n = 1024` takes seconds). The number of cyclic factors of each copy of `X(λ, i)` is `2^{|I| + k − 1} = dim T(λ)/2`.

**Example.** For `n = 6` the families are `λ = 6, 4, 2` with `m_6(6) = 1`, `m_4(6) = 4`, `m_2(6) = 4`.
- `λ = 6` (`7 = 4 + 2 + 1`, `k = 2`, `I = {0, 1}`, `h_0 = h_1 = 1`), shift `0`: small clocks `{1: 4}`; raw clocks of `∅, {0}, {1}, {0,1}`: `∞, 6, 6, 3` (for `{0}`: `ξ = 5` and `φ(5) + κ(0, 5) + h_0 = 5 + 0 + 1`; for `{1}`: `ξ = 3` and `φ(3) + κ(1, 3) + h_1 = 3 + 2 + 1`); no pooling.
- `λ = 4` (`5 = 4 + 1`, `k = 2`, `I = {0}`, `h_0 = 2`), shift `1`: small clocks `{1: 2}`; raw clocks `φ(5) + κ(0, 5) = 5` and `φ(3) + κ(1, 3) + 2 = 3 + 2 + 2 = 7`. The sequence `5, 7` increases, so it is pooled: `6, 6`.
- `λ = 2` (`3 = 2 + 1`, `k = 1`, `I = {0}`, `h_0 = 1`), shift `2`: no small clocks; raw clocks `φ(3) + κ(1, 3) = 5` and `φ(1) + κ(2, 1) + 1 = 2`.

So `Syl_2 K(Q_6) = {1: 4} ⊕ {6: 2, 3: 1} ⊕ 4·{1: 2, 6: 2} ⊕ 4·{5: 1, 2: 1} = {1: 12, 2: 4, 3: 1, 5: 4, 6: 10}`, as the direct computation gives. This is the smallest cube in which pooling acts.

**An equivalent form.** For `i ≥ 1`, with `m := i − 1` and `K := 2^k`, define for `μ ≥ 0`
  `R_μ(D) := Σ_{t∈D} (h_t − 2^t) − κ(μ, o_D)`,  `x_D := R_m(D) − R_{m+K}(I ∖ D)`.
Then `u_i(D) = k + K + κ(m, K) + x_D` for every dancer (Proposition 5.3), so the big clocks are `k + K + κ(m, K)` plus the integer antitonic fit of `x`. This is the form in which the proof computes them.

### 1.3 The fold law: dry and wet

Let `𝟙 = (1, …, 1)`. The **folded `n`-cube** is the quotient graph `Q_n/⟨𝟙⟩`: its vertices are the `2^{n−1}` pairs of antipodal words, and two pairs are joined once for each pair of words, one from each, that differ in one letter. It is the Cayley graph of `𝔽_2^n/⟨𝟙⟩` with the images of the unit vectors; for `n ≥ 3` it is a simple `n`-regular graph. We write `K̄(n)` for its sandpile group.

**A naming trap.** In the literature on interconnection networks the «folded hypercube `FQ_m`» is `Q_m` with the antipodal matching added: `2^m` vertices, degree `m + 1` [EL91]. It is the Cayley graph of `𝔽_2^m` with the unit vectors and `𝟙`, which is our folded cube in dimension `m + 1`: **our folded `n`-cube `Q_n/⟨𝟙⟩` is `FQ_{n−1}`.** We keep the index `n` of the cube that is folded.

> **Theorem DW (the fold law).** For every `n ≥ 1`,
>   **`Syl_2 K̄(n) ≅ 2·Syl_2 K(Q_n)`,**
> where `2·A` is the subgroup of doubles. Equivalently,
>   **`Syl_2 K(Q_n) ≅ (ℤ/2)^{a_n} ⊕ (Syl_2 K̄(n) with every exponent raised by one)`,  `a_n = 2^{n−2} − 2^{⌊(n−2)/2⌋}`.**

Here `a_n` is the number of factors `ℤ/2` of `K(Q_n)`, by Bai [Bai03, Theorem 1.3] (re-proved in §9.1). Theorem DW is proved family by family (§10): the folded cube splits over the same tilting families with the same multiplicities, and the group of each family is halved.

The names «dry and wet» and «dance» are explained in §1.7.

**Example.** For `n = 5`, `Syl_2 K(Q_5) = {1: 6, 3: 4, 4: 1, 6: 4}` and `a_5 = 6`, so `Syl_2 K̄(5) = {2: 4, 3: 1, 5: 4}`.

> **Corollary 1.4 (the sandpile group of the folded cube).** For every `n ≥ 2`, `Syl_2 K̄(n)` is the group of the Main Theorem with the `a_n` factors `ℤ/2` removed and every other exponent lowered by one. For every odd prime `p`, `Syl_p K̄(n) ≅ Syl_p ⊕_{j even, 2 ≤ j ≤ n} (ℤ/2j)^{C(n,j)}`.

The odd part is [GMMY24, Proposition 1.9]: the Laplacian eigenvalues of the folded cube are `2|J|` for the subsets `J ⊆ {1, …, n}` of even size. We found no earlier computation of the sandpile group of the folded cube; its order, the number of spanning trees, is the sequence OEIS A193134 [OEIS] (for `n ≥ 3`; at `n = 2` that sequence counts the simple graph `K_2`, while our `Q_2/⟨𝟙⟩` has a double edge).

**The mod-2 layer.** Theorem DW explains a coincidence noted by Gao et al. [GMMY24, Remark 2.13]: the `𝔽_2`-rank of the Laplacian of the folded cube `Q_n/⟨𝟙⟩` and the number of factors `ℤ/2` of `K(Q_n)` are both `a_n` («We are not sure if that is a coincident, or a special case of some deeper connection»). Under the fold law every factor of `Syl_2 K(Q_n)` other than the factors `ℤ/2` keeps a non-trivial image, so the number of even invariant factors of the folded Laplacian is `(2^{n−1} − 1 − a_n) + 1`, and its `𝔽_2`-rank is `2^{n−1}` minus that number, which is `a_n` (§10.8). The fold law is specific to the antipodal involution: the quotient by `x_1x_2` does not halve the group (we checked `3 ≤ n ≤ 12`, §12).

### 1.4 Consequences

> **Corollary 1.5 (Bai [Bai03, Theorems 1.1, 1.3]).** `Syl_2 K(Q_n)` has exactly `2^{n−1} − 1` cyclic factors, and exactly `a_n` of them are `ℤ/2` (`n ≥ 2`).

Bai states the first count for the invariant factors of `K(Q_n)`. They are all even [Bai03, Lemma 2.2, Corollary 2.3]: in his proof the Smith form of the Laplacian of `Q_n` has `2^{n−1}` entries `1`, and the others are those of a matrix with even entries. So his count is the number of cyclic factors of `Syl_2 K(Q_n)`.

Write `c_1(Q_n) ≥ c_2(Q_n) ≥ ⋯` for the exponents of the cyclic factors of `Syl_2 K(Q_n)`, in decreasing order, and `g(N) := max_{1≤x<N} φ(x) = max_{1≤x<N}(x + v_2 x)`. (Gao et al. write `c_i(Q_n)` for the `i`-th largest invariant factor of `K(Q_n)` and state their results for its `2`-adic valuation, which is our `c_i(Q_n)`.)

> **Corollary 1.6 (the podium).** Put `G := g(n − 1)`. For every `n ≥ 4`:
> - `n` even: `c_1 = max(G, φ(n) − 1)` and `c_2 = ⋯ = c_{n+1} = G`;
> - `n` odd and `φ(n − 1) ≤ G`: `c_1 = ⋯ = c_{n+1} = G`;
> - `n` odd and `φ(n − 1) > G`: `c_1 = ⋯ = c_{n−1} = φ(n − 1)`, `c_n = max(G, φ(n − 1) − 2)`, `c_{n+1} = G`.
>
> In particular:
> - `c_1 = max(g(n), v_2 n + n − 1)` and `c_2 = ⋯ = c_{n−1} = g(n)` for `n ≥ 3` [GMMY24, Theorems 4.1, 4.2];
> - **`c_n = max(g(n − 1), v_2(n − 1) + n − 3)` for `n ≥ 3`** [GMMY24, Conjecture 4.14];
> - **`c_{n+1} = g(n − 1)` for `n ≥ 4`** [MGM19].

> **Corollary 1.7 ([GMMY24, Conjecture 5.4]).** For every `e ≥ 1`,
>   `Syl_2 K(Q_{2^e}) ≅ Syl_2 K(Q_{2^e − 1})^2 ⊕ ℤ/2^{2^e + e − 1}`.

The proof of Corollary 1.7 gives more: each tilting family of the cube of dimension `2^e − 1` becomes one family of the cube of dimension `2^e` with the same multiplicity, and each of its dancers becomes two dancers with the same raw clock (§9.3).

### 1.5 The idea of the proof

1. **The group ring as an `SL_2`-module (§2).** In the group ring `ℤ[(ℤ/2)^n]` the Laplacian is multiplication by `σ = Σ_i (1 − x_i)`. In the basis `s_S = ∏_{i∈S}(1 − x_i)` it becomes `U + 2D`, with `U` the raising operator of the Boolean lattice and `D` the rank (up to the sign `(−1)^{|S|}`, this basis is the change of variables `u_i = x_i − 1` in the proof of [GMMY24, Proposition 2.5], and it is the Laplacian analogue of [CSX17, §5]). Identifying `s_S` with a pure tensor of `V^{⊗n}`, `V = ℤ^2` the natural module of `SL_2`, gives `σ = F + n − H`, an element of the hyperalgebra of `SL_2` over `ℤ`.
2. **The family decomposition (§3).** Over `ℤ_2`, `V^{⊗n}` is a direct sum of explicit lattices `T(λ)`, built from `ℤ` by two operations: a lattice form `Φ` of the Frobenius twist (`T(2l+1) = Φ(T(l))`) and the tensor product with `V` (`T(2l+2) = V ⊗ Φ(T(l))`). The proof needs only an elementary lifting lemma for `SL_2`. Since `σ` is carried by every isomorphism, the group splits family by family.
3. **The dance (§4).** On `Φ(N)` half of the relations have unit pivots; eliminating them leaves twice the same kind of operator on `N`, with the payment of each floor replaced by a product of two consecutive payments. On `V ⊗ Φ(N)` the same happens with two coupled «dancers». After `k` moves `X(λ, i)` is the small clocks plus `coker(2^k M(λ, i))` (the Smith exponents of `M` raised by `k`), `M` an explicit triangular matrix indexed by the dancers, whose entries are products of payments over windows times the coefficients of an explicit polynomial (Theorem D). Its entries have valuations given by carries (§5).
4. **The Smith form of `M` (§6–§8).** The `r`-th determinantal divisor `d_r` of `M` is bounded below by the cheapest `r`-matching in the support of `M`, valued by `v_2` (the tropical bound). It is at most the valuation of one natural minor, which has a unique cheapest matching (Theorem O); that valuation is a partial sum of the raw clocks, and convexity turns it into the partial sum of the pooled clocks (Lemma 6.4). Theorem F shows that every `r`-matching costs at least the partial sums of the pooled clocks, by a potential built digit by digit from the bottom of `λ + 1`. The two bounds meet.
5. **The fold (§10).** On each family the antipode acts as `±exp(F)`. The folded group is the cokernel of an operator that differs from the doubled one by a perturbation `Σ ζ_m F^{(m)}` of higher divided powers. The same dance applies to both. Every move stays clean because the coefficients of every level lie in a ring `𝒦` of `2`-adic functions of twice the position, on which a shift-invariant reduction makes every Schur complement vanish modulo `2` (Theorem 10.15). The perturbation then changes no valuation of the final matrix (Theorem 10.12). The even families are glued pairs of odd ones, and the glue survives the dance.

### 1.6 Notation and conventions

| symbol | meaning | first use |
|---|---|---|
| `Q_n`, `K(Q_n)`, `K̄(n)` | the `n`-cube, its sandpile group, that of the folded cube `Q_n/⟨𝟙⟩` | §1.1, §1.3 |
| `s_2`, `v_2`, `κ(a, b)`, `φ(x)` | binary digit sum, `2`-adic valuation, carries of `a + b`, `x + v_2 x` | §1.2 |
| `λ`, `k`, `K`, `I` | a family: `λ + 1 = 2^k + Σ_{t∈I} 2^t`, `K = 2^k` | §1.2 |
| `D`, `o_D`, `h_t`, `h(D)` | dancers `D ⊆ I`, `Σ_{t∈D} 2^t`, gaps `next(t) − t`, `Σ_{t∈D} h_t` | §1.2 |
| `i`, `m` | the shift `(n − λ)/2`, and `m = i − 1` when `i ≥ 1` | §1.2 |
| `m_λ(n)` | multiplicity of the family `λ` in `V^{⊗n}` | §1.2, §3 |
| `u_i(D)`, `ŷ_i(D)`, `X(λ, i)` | raw clocks, pooled clocks, the group of a family | §1.2 |
| `R = ℤ[(ℤ/2)^n]`, `s_S`, `σ` | the group ring, its basis `∏_{i∈S}(1 − x_i)`, the Laplacian element | §2 |
| `V`, `b_0`, `b_1`, `E`, `F`, `H`, `F^{(r)}` | the natural module of `SL_2`, its basis, the hyperalgebra generators | §2 |
| `A = ℤ_2` | the base ring | §2.2 |
| `Δ_A(λ)`, `∇_A(λ)` | Weyl and dual Weyl lattices | §2.3 |
| `Φ(N)`, `T(λ)` | the doubling functor, the dance lattices | §3 |
| `D` (operator), `π(d)`, `σ^{(α)}_i` | the floor operator, a payment, `F + 2^α(D + i)` | §2.2, §3.4, §4 |
| `M(λ, i)`, `q_k`, `a_k(Δ)`, `δ(Δ)` | the final matrix, the coefficient polynomial, its coefficients and their valuations | §4.4, §4.5 |
| `R_μ(D)`, `γ(Δ)`, `x_D`, `ψ(E)` | rulers, gold, clocks of a cell, `Σ_{t∈E}(h_t − 2^t)` | §1.2, §5 |
| `d_r`, `T(r)`, `U(r)`, `Y(r)` | determinantal divisors, cheapest `r`-matching, natural and pooled partial sums | §6 |
| `a = x_1⋯x_n`, `τ_i`, `Ψ_j` | the antipode, the family operator, the folded odd-family operator | §10 |
| `𝒦`, `Θ`, `𝒯_h` | the ring of functions `ϑ(y) = a + 2χ(2y)`, its reduction, the covariant systems of level `h` | §10.5 |

A few letters have two meanings, each clear from its argument: `D` is a dancer (a subset of `I`) and the floor operator of §4; `K` is `2^k` and the sandpile group `K(·)`; `T(λ)` is a dance lattice and `T(r)` a cheapest-matching value; `τ_t` is a datum of a window (§7.3) and `τ_i` the family operator of §10; and «window» is a range of floors in §4.4 and a range of binary digits in §7.3. Groups are written additively. «Lattice» means a finitely generated free `ℤ_2`-module, and for a square matrix `M` over `ℤ_2` with non-zero determinant, `coker M` and its Smith form are taken over `ℤ_2`.

### 1.7 Vocabulary, and why these names

Some words in this paper are ours. Each is defined where it first matters; this table gives its standard meaning.

| our word | standard meaning | where |
|---|---|---|
| family `λ`; shift `i` | the summand `T(λ)` of `V^{⊗n}` (Theorem 3.6); the integer `i = (n − λ)/2`, so that the Laplacian acts on `T(λ)` as `F + λ − H + 2i` | §1.2, §3.4 |
| dance lattice `T(λ)` | a `ℤ_2`-lattice whose reduction modulo `2` is the indecomposable tilting module of `SL_2` of highest weight `λ` in characteristic `2` (Remark (1) after Theorem 3.6) | §3.3 |
| dancers; o-order | the subsets `D ⊆ I`, which index the slots after the dance; their order by `o_D = Σ_{t∈D} 2^t` | §1.2, §4.3 |
| floor | the grading by `(c − w)/2` on the weight `w`; `F` raises it by one | §2.2 |
| payment; payment system | a diagonal operator given by a function of the floor; the operator `F` plus payments on copies of a lattice, with lower-triangular couplings between the copies | §4.1 |
| twist move; split move | one step of block Gaussian elimination: eliminate the unit pivots, take the Schur complement, divide by `2`. The split move first separates the two basis vectors of `V`, so that each dancer becomes two | §4.2, §10.3 |
| the dance | the `k` moves, one for each binary digit of `λ + 1` below the leading one | §4.3 |
| final matrix; window | the triangular matrix `M(λ, i)` of size `2^{|I|}` left by the dance; the range of floors whose payments are multiplied in one of its entries | §4.4 |
| clock | a cyclic factor `ℤ/2^e`, named by its exponent `e`; the small clocks come from the eliminated pivots, the big clocks from the final matrix | §1.2, §4.3 |
| raw clocks; pooling | explicit integers `u_i(D)`; their antitonic least-squares fit (isotonic regression, by pool-adjacent-violators), which in the cube is always an integer sequence (Lemma 7.9) | §1.2, §7.1 |
| cell | the data `(λ, i, α)` of one final matrix | §5, §6.1 |
| ruler; gold | the row and the column term of the valuation of an entry of the final matrix; the remaining term `γ`, which vanishes exactly on the golden arrows | §5, §6.2 |
| golden matching | the unique bijection `β_r` all of whose arrows are golden; its term is the unique term of least valuation in the expansion of the natural minor | §6.2 |
| mirror | the map `D ↦ I ∖ D`, which reverses the o-order | §6.1, §7.1 |
| ceiling; floor (of the Smith form) | the upper and the lower bound for the determinantal divisors of the final matrix (Theorems O and F); this «floor» is not the grading | §6, §7 |
| house; penalties | the binary data `(I, k, ℓ, α)` of a cell, freed from `λ` and `i`; the two correction terms of a real cell | §7.3 |
| windows `W_t`; gates | the intervals of binary digits `[t, next(t))`; the rule by which each of them lets a carry through (Lemma 7.6) | §7.3 |
| podium | the `n + 1` largest cyclic factors of `Syl_2 K(Q_n)` | §1.4, §9.2 |
| the fold | the quotient by the antipode `𝟙`, which gives the folded cube | §1.3, §10 |
| dry; wet | reduction modulo `2`; the lattice over `ℤ_2` | below |
| arms; glue; bend | the two odd-family operators that make an even family; the triangular block form `glue(X, Y)` that joins them; the estimate by which the two sides of the fold law differ by a unit at the end of the dance (Lemma 10.20) | §10.2, §10.7 |
| formal dance; positions; covariant system | the dance of operators with divided powers `F^{(m)}`; the numbers `2^h f + o_D + c`; a system whose coefficients depend only on `Δ = D ∖ D'`, on `m` and on the position of the target | §10.3, §10.5 |
| turned lid | a symmetry that we measured and did not prove | §11 |

**Why «dance».** Read the binary word of `λ + 1` from the bottom. At a digit `0` every dancer makes the same step, the twist move. At a digit `1` every dancer splits into two partners, the split move. After `k` digits there are `2^{|I|}` dancers, the subsets of `I`. At the start each floor `d` pays the even amount `2^α(i + d)`; each move gives every new floor a payment equal to minus half the product of the payments of two adjacent old floors, so every payment stays even; at the end the final matrix records who owes what to whom. The sand is the sandpile; the dance is the elimination that brings it to rest.

**Why «dry» and «wet».** Modulo `2` — dry — the module `T(2l + 1)` becomes `V ⊗ T(l)^{[1]}`, the tensor product of `V` with a Frobenius twist (Proposition 3.1(c)), and the cokernel of the Laplacian modulo `2` sees only the number of cyclic factors of the `2`-part. Over `ℤ_2` — wet — the twist has an integral form, the lattice `Φ(T(l))` of §3.1, on which `F^2` acts as `2F` of `T(l)`, and every power of `2` survives. The fold dries the cube by exactly one layer: the factors `ℤ/2` disappear, and every other exponent drops by one (Theorem DW).

### 1.8 Literature and priority

**What is ours, to the best of our knowledge**, after a search of the literature up to October 2026 (arXiv and journal searches, the citation trees of [Bai03], [CSX17] and [GMMY24] in Google Scholar and Semantic Scholar, and the sources listed below; MathSciNet was not searched):
1. the whole `2`-part of `K(Q_n)`, for every `n` (the Main Theorem);
2. the decomposition of a sandpile group over tilting modules, with the reduction of each piece to a small explicit matrix (Theorems 3.6 and D) — we found no tilting decomposition of any sandpile group;
3. proofs of [GMMY24, Conjectures 4.14 and 5.4] and of the `(n+1)`-th factor of [MGM19] — we found no other proof;
4. the fold law and the sandpile group of the folded cube (Theorem DW, Corollary 1.4);
5. the proof techniques of §4–§7 and §10 as combinations: the dance, the cost form with carries, Theorems O, U and F, the ring `𝒦` with Theorem 10.15, and Theorem 10.12. Each ingredient we did not invent is credited where it is used.

**What is not ours.** Bai determined the odd part and proved Reiner's two counts [Bai03]. Gao, Marx-Kuo, McDonald and Yuen determined the `n − 1` largest factors and posed the conjectures we prove; their Proposition 1.9 gives the odd part of every Cayley graph of `𝔽_2^r`, their Proposition 2.12 the `𝔽_2`-rank of the Laplacian of the folded cube (§10.8), their Remark 4.4 contains Lemma 9.2(b), their Table 1 reproduces Bai's table of `Syl_2 K(Q_n)` for `n ≤ 11`, and the monomials of their change of variables `u_i = x_i − 1` (proof of their Proposition 2.5) are, up to the sign `(−1)^{|S|}`, the basis we use [GMMY24]. Chandler, Sin and Xiang computed the Smith group of the adjacency matrix with the same monomial basis and Bier's vectors [CSX17], [Bie93], [Wil90]. Reiner and Tseng gave the exact sequence relating the critical groups of a double cover and of its base [RT14]; we use none of it, but the fold law is a statement about such a cover. The multiplicities of tilting modules of `SL_2` in tensor powers of `V` in characteristic `2` are known: they follow from Donkin's tensor product theorem [Don93] and the characters of [TW21], and Larsen gives the fusion rule of `V^{⊗2}` at `p = 2` [Lar24, §2], which reproduces our recursion (§12.2). The Weyl and dual Weyl filtrations, and the lifting of tilting decompositions over complete rings, are standard [Jan03, Don93]; we give the short elementary proofs needed for `SL_2` over `ℤ_2` (§3.2), because the general references are written over fields or for other purposes. Kostant's commutation formula in the `ℤ`-form of `U(sl_2)` is [Kos66], [Hum72, §26]. Kummer's theorem [Kum52], Legendre's formula `v_2(m!) = m − s_2(m)`, the von Staudt–Clausen theorem [vSt40], [Cla40], Strassmann's theorem [Str28], and the pool-adjacent-violators algorithm [ABERS55] are classical. Related representation-theoretic computations of Smith and critical groups are those of Sin's school [CSX17], [DHS18] and the subset-intersection diagonal forms of [DEGJPP23].

**Contemporary context.** Vetluzhskikh and Zakharov compute the order of the kernel of the pushforward between critical groups of abelian covers [VZ24], and Len and Zakharov the order of the Prym group of a double cover [LZ22]; both give orders, not group structure. Akyar et al. recall that the exact sequence of Reiner and Tseng for a graph cover splits on primary components away from the primes dividing the covering degree, which makes the prime `2` «a natural place to look for additional structure under an involution» [Aky26, §4]. Their reflections of odd grids have fixed vertices, so their fold is not a regular double cover, and they ask: «Can an analogous integral description with fixed vertices explain both the folded all-ones class and the remaining 2-primary factors?» The antipodal fold of the cube has no fixed vertex: it is a regular double cover, and there the fold law describes the `2`-part.

**If a result here was obtained earlier, we would be grateful to be told, and we will correct the record.**

## 2. The group ring as a module over the hyperalgebra of `SL_2`

### 2.1 The Laplacian in the group ring

Let `G = (ℤ/2)^n` with generators `x_1, …, x_n`, and `R := ℤ[G]`. The Laplacian of the Cayley graph `Q_n` of `G` acts on `ℤ^G = R` as multiplication by
  `σ := Σ_{i=1}^{n} (1 − x_i)`.
Since `Q_n` is connected, `coker(σ on R) ≅ ℤ ⊕ K(Q_n)` [Lor91], [Big99]. Put `s_i := 1 − x_i` and, for `S ⊆ {1, …, n}`, `s_S := ∏_{i∈S} s_i`. The elements `s_S` form a `ℤ`-basis of `R` (the change of basis from `{x_S}` is unitriangular for inclusion).

**Lemma 2.1.** In `R`,
  `s_j s_S = s_{S∪{j}}` if `j ∉ S`,  `s_j s_S = 2 s_S` if `j ∈ S`.
Hence `σ s_S = Σ_{j∉S} s_{S∪{j}} + 2|S|·s_S`, that is, **`σ = U + 2D`**, where `U s_S = Σ_{j∉S} s_{S∪{j}}` and `D s_S = |S| s_S`.

*Proof.* `s_j^2 = (1 − x_j)^2 = 2 − 2x_j = 2s_j`. ∎

Up to the sign `(−1)^{|S|}`, these are the monomials of the change of variables `u_i = x_i − 1` used by Gao et al. [GMMY24, proof of Proposition 2.5], and the basis is the Laplacian analogue of the monomial basis in which Chandler, Sin and Xiang write the adjacency matrix [CSX17, §5, (5)]. Since `(ℤ ⊕ K) ⊗ ℤ_2 ≅ ℤ_2 ⊕ Syl_2 K` for a finite abelian group `K`, and `⊗ ℤ_2` is right exact, we have **`ℤ_2 ⊕ Syl_2 K(Q_n) ≅ coker(σ on R ⊗ ℤ_2)`.**

### 2.2 The hyperalgebra and the dictionary

Let `U_ℚ` be the universal enveloping algebra of `sl_2` over `ℚ`, with generators `E, F, H`, `[H, E] = 2E`, `[H, F] = −2F`, `[E, F] = H`. Its Kostant `ℤ`-form `Dist_ℤ` is the subring generated by the divided powers `E^{(r)} = E^r/r!`, `F^{(r)} = F^r/r!` and the elements `C(H, r) = H(H−1)⋯(H−r+1)/r!` [Kos66], [Hum72, §26]; it is the distribution algebra of `SL_2` over `ℤ`. Kostant's formula
  **(K)** `E^{(s)} F^{(r)} = Σ_{j=0}^{min(r,s)} F^{(r−j)} C(H − r − s + 2j, j) E^{(s−j)}`
holds in `U_ℚ`. Put `A := ℤ_2` and `Dist_A := A ⊗ Dist_ℤ`, a Hopf algebra with `Δ(F^{(r)}) = Σ_{a+b=r} F^{(a)} ⊗ F^{(b)}`, the same for `E`, and `Δ(H) = H ⊗ 1 + 1 ⊗ H`.

A **lattice** is a `Dist_A`-module that is free of finite rank over `A`, on which `H` acts diagonally with integer eigenvalues (the **weights**): the module is the direct sum of its weight spaces. A lattice `X` has the **floor** grading for any integer `c ≥` every weight of `X` with `c ≡` the weights `(mod 2)`: the floor of a weight vector of weight `w` is `(c − w)/2`. We write `D` for the floor operator (the floor relative to the top weight, unless said otherwise); `F` raises the floor by one.

Let `V := A b_0 ⊕ A b_1` with `H b_0 = b_0`, `H b_1 = −b_1`, `F b_0 = b_1`, `E b_1 = b_0`, `F b_1 = E b_0 = 0`, and `E^{(r)} = F^{(r)} = 0` on `V` for `r ≥ 2`: the natural module.

**Lemma 2.2 (the dictionary).** The `A`-linear isomorphism `R ⊗ A → V^{⊗n}` that sends `s_S` to the pure tensor with `b_1` in the positions of `S` and `b_0` elsewhere carries `U` to `F`, `D` to `(n − H)/2`, and therefore
  **`σ = F + n − H`**.

*Proof.* On `V^{⊗n}`, `F = Σ_j 1 ⊗ ⋯ ⊗ F ⊗ ⋯ ⊗ 1` turns one `b_0` into `b_1` in every possible way, which is `U`; and a pure tensor with `|S|` letters `b_1` has weight `n − 2|S|`. ∎

**Corollary 2.3.** If `V^{⊗n} ≅ ⊕_j M_j` as `Dist_A`-modules, then `ℤ_2 ⊕ Syl_2 K(Q_n) ≅ ⊕_j coker(F + n − H on M_j)`.

*Proof.* `σ = F + n − H` is an element of `Dist_A` (it acts through `F` and `H`), so every isomorphism of `Dist_A`-modules carries `σ` to `σ`, and the cokernel of an endomorphism that preserves a direct sum decomposition is the sum of the cokernels. ∎

### 2.3 Weyl lattices, duality, filtrations

For `λ ≥ 0` let `Δ_ℚ(λ)` be the simple `U_ℚ`-module of highest weight `λ` with highest weight vector `v`, and `Δ_A(λ) := Dist_A·v`, the **Weyl lattice**. It has the basis `e_r := F^{(r)} v` (`0 ≤ r ≤ λ`), with
  `F e_r = (r + 1) e_{r+1}`,  `E e_r = (λ − r + 1) e_{r−1}`,  `H e_r = (λ − 2r) e_r`.
Let `ι` be the anti-involution of `Dist_A` with `ι(E^{(r)}) = F^{(r)}`, `ι(F^{(r)}) = E^{(r)}`, `ι(H) = H`. For a lattice `X` the **contravariant dual** `X^ι := Hom_A(X, A)` with `(g·ξ)(x) := ξ(ι(g)x)` is a lattice; `ι` is compatible with the coproduct, so `(X ⊗ Y)^ι ≅ X^ι ⊗ Y^ι`, and `V^ι ≅ V` (the dual basis of `b_0, b_1`). The **dual Weyl lattice** is `∇_A(λ) := Δ_A(λ)^ι`; in the dual basis `w_r` of the `e_r`,
  `F w_r = (λ − r) w_{r+1}`,  `E w_r = r w_{r−1}`.
A **`Δ`-filtration** of a lattice `X` is a chain of sublattices `0 = X_0 ⊂ X_1 ⊂ ⋯ ⊂ X_s = X`, each `X/X_j` free over `A`, with `X_j/X_{j−1} ≅ Δ_A(λ_j)`; a **`∇`-filtration** is the same with `∇_A`. The map `ι` exchanges them.

**Lemma 2.4.** For `m ≥ 1`, `Δ_A(m) ⊗ V` has a `Δ`-filtration with factors `Δ_A(m + 1)` (a sublattice) and `Δ_A(m − 1)` (the quotient), and `∇_A(m) ⊗ V` a `∇`-filtration with factors `∇_A(m − 1)`, `∇_A(m + 1)`. Moreover, `Δ_A(0) ⊗ V = V = Δ_A(1) = ∇_A(1)`.

*Proof.* Let `v` be the highest weight vector of `Δ_A(m)`. The vectors `F^{(r)}(v ⊗ b_0) = F^{(r)}v ⊗ b_0 + F^{(r−1)}v ⊗ b_1` (`0 ≤ r ≤ m + 1`) are primitive in the basis `{F^{(r)}v ⊗ b_e}`, so they span a saturated sublattice `X_1`; it is `Dist_A·(v ⊗ b_0)`. Over `ℚ`, `X_1 ⊗ ℚ` is generated by a vector of weight `m + 1` killed by every `E^{(s)}`, `s ≥ 1`, and has dimension `m + 2`, so it is the simple module `Δ_ℚ(m + 1)`, with `v ⊗ b_0` as highest weight vector; and `Dist_A` applied to the highest weight vector gives `Δ_A(m + 1)` on one side and `X_1` on the other. So `X_1 ≅ Δ_A(m + 1)`. The quotient is free of rank `m`, spanned by the images of `F^{(s)}v ⊗ b_1` (`0 ≤ s < m`): indeed `F^{(m)}v ⊗ b_1 = F^{(m+1)}(v ⊗ b_0) ∈ X_1`. The image `v'` of `v ⊗ b_1` is killed by `E` (`E(v ⊗ b_1) = v ⊗ b_0 ∈ X_1`) and by every `E^{(s)}`, `s ≥ 2`, and `F^{(s)}(v ⊗ b_1) = F^{(s)}v ⊗ b_1` (since `F^{(r)} b_1 = 0` for `r ≥ 1`); so the quotient is `Dist_A·v' ≅ Δ_A(m − 1)`. The statement for `∇` follows by the duality `ι`. ∎

## 3. The dance lattices and the family decomposition

### 3.1 The doubling functor

Let `N` be a lattice. On the free `A`-module `Φ(N) := b_0 ⊗ N ⊕ b_1 ⊗ N` (we write `b_e n` for `b_e ⊗ n`) define, for `n` of weight `w`,
  `H(b_0 n) = (2w + 1) b_0 n`,  `H(b_1 n) = (2w − 1) b_1 n`,
  `F(b_0 n) = b_1 n`,  `F(b_1 n) = 2 b_0 (F n)`,
  `E(b_0 n) = 2 b_1 (E n)`,  `E(b_1 n) = b_0 (Ω − H^2) n`,
where `Ω := 4FE + (H + 1)^2` acts on `N`; on a vector of weight `w`, `Ω − H^2 = 4FE + 2w + 1`. For a morphism `f` of lattices put `Φ(f) := 1 ⊗ f`.

**Proposition 3.1.**
(a) `Φ(N)` is a lattice, `Φ` is an exact functor, and it sends saturated sublattices to saturated sublattices.
(b) On `Φ(N)`, for `s ≥ 0` and `e = 0, 1`:
  `F^{(2s)}(b_e n) = b_e F^{(s)} n /(2s − 1)!!`,  `F^{(2s+1)}(b_0 n) = b_1 F^{(s)} n /(2s + 1)!!`,
  `F^{(2s+1)}(b_1 n) = ((2s + 2)/(2s + 1)!!)·b_0 F^{(s+1)} n`.
(c) `Φ(N) ⊗ 𝔽_2 ≅ V ⊗ (N ⊗ 𝔽_2)^{[1]}` as `Dist_{𝔽_2}`-modules, where `M^{[1]}` is the Frobenius twist (`F^{(2s)}`, `E^{(2s)}` act as `F^{(s)}`, `E^{(s)}`, the odd divided powers act as `0`, and `H` acts as `2H`).
(d) `Φ(Δ_A(μ)) ≅ Δ_A(2μ + 1)` and `Φ(∇_A(μ)) ≅ ∇_A(2μ + 1)`; `Φ(A) = V`.

*Proof.* (a) *The relations.* On `b_0 n` (weight `2w + 1`): `EF(b_0 n) = E(b_1 n) = b_0(4FE + 2w + 1)n` and `FE(b_0 n) = F(2 b_1 E n) = 4 b_0 FE n`, so `[E, F] = 2w + 1`. On `b_1 n` (weight `2w − 1`): `EF(b_1 n) = 4 b_1 EF n` and `FE(b_1 n) = b_1(4FE + 2w + 1)n`, so `[E, F] = 4(EF − FE) − 2w − 1 = 4w − 2w − 1 = 2w − 1`. The relations with `H` hold by weights. So `Φ(N) ⊗ ℚ` is a `U_ℚ`-module, and `Φ(N)` is stable under `F` and `H`.
*Divided powers.* From the formulas, `F^{2s}(b_0 n) = 2^s b_0 F^s n`, `F^{2s+1}(b_0 n) = 2^s b_1 F^s n`, `F^{2s}(b_1 n) = 2^s b_1 F^s n`, `F^{2s+1}(b_1 n) = 2^{s+1} b_0 F^{s+1} n`; dividing by `(2s)! = 2^s s!(2s − 1)!!` and `(2s+1)! = 2^s s!(2s+1)!!` gives (b), whose denominators are odd. For `E`, `Ω` is central in `U_ℚ` and integral, and `E f(H) = f(H − 2) E`; by induction, on `n` of weight `w`,
  `E^{2s}(b_1 n) = 2^s ∏_{0≤j<s}(Ω − (w+2j)^2)·b_1 E^s n`,  `E^{2s+1}(b_1 n) = 2^s ∏_{0≤j≤s}(Ω − (w+2j)^2)·b_0 E^s n`,
  `E^{2s}(b_0 n) = 2^s ∏_{1≤j≤s}(Ω − (w+2j)^2)·b_0 E^s n`,  `E^{2s+1}(b_0 n) = 2^{s+1} ∏_{1≤j≤s}(Ω − (w+2j)^2)·b_1 E^{s+1} n`;
dividing by the factorials leaves `E^{(s)}` or `E^{(s+1)}` of `N` times odd denominators (`2(s+1)/(2s+1)!!` for the last one). The `C(H, r)` act by integers. So `Φ(N)` is stable under `Dist_A`, and it is a lattice. The map `Φ(f) = 1 ⊗ f` commutes with all the formulas because they use only the action on `N`; exactness and saturation are clear because `Φ(N) = N^2` as `A`-modules.
(c) On a vector of weight `w + 2s`, `Ω ≡ (H + 1)^2 (mod 4)`, so `Ω − (w + 2j)^2 ≡ (w + 2s + 1)^2 − (w + 2j)^2 = (2s − 2j + 1)(2w + 2s + 2j + 1)`, an odd number, modulo `2`. Hence modulo `2`, `F^{(2s)}` and `E^{(2s)}` act as `1 ⊗ F^{(s)}`, `1 ⊗ E^{(s)}`; `F^{(2s+1)}(b_0 n) = b_1 F^{(s)}n`, `F^{(2s+1)}(b_1 n) = 0`, `E^{(2s+1)}(b_1 n) = b_0 E^{(s)} n`, `E^{(2s+1)}(b_0 n) = 0`. These are the formulas of `V ⊗ M^{[1]}` computed with the coproduct, since on `M^{[1]}` only the even divided powers act.
(d) Order the basis of `Φ(∇_A(μ))` by weight: `b_0 w_s` (index `2s`), `b_1 w_s` (index `2s + 1`). Then `F(b_0 w_s) = b_1 w_s` and `F(b_1 w_s) = 2(μ − s) b_0 w_{s+1}`, while in `∇_A(2μ + 1)`, `F w'_R = (2μ + 1 − R) w'_{R+1}`, that is `2μ + 1 − 2s` for `R = 2s` and `2(μ − s)` for `R = 2s + 1`. The diagonal map `w'_R ↦ c_R·(R-th vector)` with `c_{2s} = (2μ + 1 − 2s)c_{2s+1}`, `c_{2s+1} = c_{2s+2}`, `c_0 = 1`, has odd ratios, so it is an isomorphism of `A`-modules; it commutes with `F` and `H`. Over `ℚ` both modules are simple: `Φ(∇_A(μ)) ⊗ ℚ` has the character of `Δ(2μ + 1)`, and by Weyl's theorem on complete reducibility a finite-dimensional `U_ℚ`-module with the character of a simple module is simple; and on a simple module `E` is determined by `F`, `H` and `E(top) = 0`, through `E F x = F E x + H x`; so the map commutes with `E`, hence with `Dist_A ⊗ ℚ` and with `Dist_A`. The same argument with `F e_r = (r+1)e_{r+1}` gives `Φ(Δ_A(μ)) ≅ Δ_A(2μ + 1)` (ratios `(2s+1)` and `1`). Finally, `Φ(A) = V` is (d) with `μ = 0`. ∎

### 3.2 Lifting from `𝔽_2`

**Lemma 3.2 (Lemma W).** Let `X` be a lattice with a sublattice `N` such that `X/N ≅ Δ_A(λ)` and every weight of `N` lies in `[−λ, λ]`. Then the extension splits.

*Proof.* Lift the highest weight vector `v` of `Δ_A(λ)` to `x ∈ X` of weight `λ`. Every weight of `X` lies in `[−λ, λ]`, so `E^{(s)}x = 0` for `s ≥ 1` and `F^{(r)}x = 0` for `r > λ`. Define the `A`-linear map `f: Δ_A(λ) → X` by `f(e_r) := F^{(r)}x`. Then
  `F^{(t)}f(e_r) = C(r+t, t) F^{(r+t)}x = f(F^{(t)}e_r)`
(both sides vanish when `r + t > λ`), and by (K)
  `E^{(s)}F^{(r)}x = C(λ − r + s, s) F^{(r−s)} x`,
which is the same formula as on `v`; so `f` is a `Dist_A`-map splitting the extension. ∎

**Lemma 3.3.** For all `λ, μ ≥ 0`, `Ext^1(Δ_A(λ), ∇_A(μ)) = 0` (extensions of `Dist_A`-modules; an extension `X` of two lattices is a lattice: `X ⊗ ℚ` is semisimple by Weyl's theorem, so `H` is diagonalizable on it with integer eigenvalues, and the projection onto the weight space of weight `w` is `P(H)`, where `P` is the polynomial of degree at most `w_1 − w_0` that takes the value `1` at `w` and `0` at the other integers of `[w_0, w_1]`, `w_0` and `w_1` the least and the largest weight; by Newton's forward differences
  `P(H) = Σ_r (Δ^r P)(w_0)·C(H − w_0, r)`
with integer coefficients `(Δ^r P)(w_0)`, and the `C(H − w_0, r)` lie in `Dist_ℤ`; so `X` is the direct sum of its weight spaces). Consequently, if `M` has a `Δ`-filtration and `N` a `∇`-filtration, then `Ext^1(M, N) = 0`, and the reduction map `Hom_{Dist_A}(M, N) → Hom_{Dist_{𝔽_2}}(M ⊗ 𝔽_2, N ⊗ 𝔽_2)` is onto.

*Proof.* If `μ ≤ λ`, the weights of `∇_A(μ)` lie in `[−μ, μ] ⊆ [−λ, λ]`: Lemma 3.2. If `μ > λ`, the duality `ι` identifies the group with `Ext^1(Δ_A(μ), ∇_A(λ))`, which vanishes by the first case. The long exact sequences of `Ext` along the filtrations give `Ext^1(M, N) = 0`. Applying `Hom(M, −)` to `0 → N → N → N ⊗ 𝔽_2 → 0` (the first map is multiplication by `2`) gives the exact sequence `Hom(M, N) → Hom(M, N ⊗ 𝔽_2) → Ext^1(M, N) = 0`, and
  `Hom_{Dist_A}(M, N ⊗ 𝔽_2) = Hom_{Dist_{𝔽_2}}(M ⊗ 𝔽_2, N ⊗ 𝔽_2)`. ∎

**Corollary 3.4.** Let `X, Y` be lattices that both have a `Δ`-filtration and a `∇`-filtration. If `X ⊗ 𝔽_2 ≅ Y ⊗ 𝔽_2`, then `X ≅ Y`.

*Proof.* Lift an isomorphism `f̄` and its inverse to `f: X → Y`, `g: Y → X` (Lemma 3.3). Then `gf ≡ 1 (mod 2)` in the ring `End(X)`, which is a free `A`-module of finite rank, so `gf = 1 + 2h` is invertible (`A` is complete); likewise `fg`. So `f` is an isomorphism. ∎

### 3.3 The dance lattices

Define lattices `T(λ)`, `λ ≥ 0`, by
  **`T(0) := A`,  `T(2l + 1) := Φ(T(l))`,  `T(2l + 2) := V ⊗ Φ(T(l))`.**
Reading `λ + 1` in binary from the leading digit down, `T(λ)` is obtained from `A` by `k` moves, one per binary digit below the leading one: a digit `0` is a `Φ` and a digit `1` is a `V ⊗ Φ`. If `λ + 1 = 2^k + Σ_{t∈I} 2^t`, the rank of `T(λ)` is `2^{k + |I|}`; its weights are `λ, λ − 2, …, −λ` (the top weight occurs once), and its character is
  **`ch T(λ) = ∏_{t<k} (e^{2^t} + e^{−2^t})·∏_{t∈I} (e^{2^t} + e^{−2^t})`,**
because
  `ch Φ(N) = (e + e^{−1})·(ch N)(e^2)`  and  `ch(V ⊗ M) = (e + e^{−1}) ch M`.
By Lemma 2.4 and Proposition 3.1(d), every `T(λ)` and every `V^{⊗n} ⊗ A` has a `Δ`-filtration and a `∇`-filtration (both operations preserve each kind of filtration).

**Lemma 3.5.** Over `𝔽_2`, `V^{⊗3} ≅ Δ(3) ⊕ V^2` and `Δ(3) ≅ V ⊗ V^{[1]}`. Consequently, for every lattice `N`,
  `(V ⊗ V ⊗ Φ(N)) ⊗ 𝔽_2 ≅ (Φ(N)^2 ⊕ Φ(V ⊗ N)) ⊗ 𝔽_2`.

*Proof.* The submodule of `V^{⊗3}` generated by `b_0^{⊗3}` is `Δ(3)`; its contravariant form takes the values `1, 3, 3, 1` (that is, `C(3, r)`), all units, so `V^{⊗3} = Δ(3) ⊕ Δ(3)^⊥`, and `Δ(3)^⊥` is stable because the form is contravariant. This complement has weights `±1` only; on its weight-`1` space `E = 0`, so `EF = H = 1` there, `F` maps it isomorphically onto the weight-`(−1)` space, and each pair `{p, Fp}` spans a copy of `V`: `Δ(3)^⊥ ≅ V^2`. The construction in the proof of Lemma 3.2, which works verbatim over `𝔽_2`, gives a map `Δ(3) → V ⊗ V^{[1]}`, `v ↦ b_0 ⊗ b_0`; its image contains `b_0 b_0`, `b_1 b_0`, `b_0 b_1 = F^{(2)}(b_0 b_0)` and `b_1 b_1`, so it is onto, and both have dimension `4`. Finally, with Proposition 3.1(c) and the monoidality of the twist,
  `(V ⊗ V ⊗ Φ(N)) ⊗ 𝔽_2 ≅ V^{⊗3} ⊗ N̄^{[1]} ≅ (V ⊗ V^{[1]} ⊗ N̄^{[1]}) ⊕ (V ⊗ N̄^{[1]})^2 = (V ⊗ (V ⊗ N̄)^{[1]}) ⊕ (V ⊗ N̄^{[1]})^2`,
which is `(Φ(V ⊗ N) ⊕ Φ(N)^2) ⊗ 𝔽_2` (`N̄ := N ⊗ 𝔽_2`). ∎

**Theorem 3.6 (the family decomposition).** For every `n ≥ 0`, as `Dist_A`-lattices,
  **`V^{⊗n} ⊗ A ≅ ⊕_λ T(λ)^{m_λ(n)}`,**
with the multiplicities `m_λ(n)` of §1.2.

*Proof.* Induction on `n`, applying `V ⊗ −` to the decomposition for `n − 1`; it suffices that `V ⊗ T(λ)` decomposes according to the rule `V·[λ]` of §1.2. Now `V ⊗ T(0) = V = Φ(A) = T(1)`, and `V ⊗ T(2l + 1) = V ⊗ Φ(T(l)) = T(2l + 2)` by definition. For `V ⊗ T(2l + 2) = V ⊗ V ⊗ Φ(T(l))`: both it and `Φ(T(l))^2 ⊕ Φ(V ⊗ T(l))` have `Δ`- and `∇`-filtrations, and their reductions are isomorphic (Lemma 3.5), so they are isomorphic (Corollary 3.4). Here `Φ(T(l))^2 = T(2l+1)^2`, and `V ⊗ T(l)` decomposes by induction on `l` (`Φ` is additive and `Φ(T(ν)) = T(2ν + 1)`). ∎

**Remarks.** (1) `T(λ) ⊗ 𝔽_2` is the indecomposable tilting module of `SL_2` of highest weight `λ` in characteristic `2` (Donkin's tensor product theorem [Don93]), so `m_λ(n)` is its multiplicity in `V^{⊗n}`; this identification is not used. The multiplicities are known: they can be read off by peeling the characters above off `(e + e^{−1})^n` [TW21], and Larsen gives the fusion rule of `V^{⊗2}` in characteristic `2` [Lar24, §2]; iterating Larsen's rule reproduces the recursion of §1.2 for every even `n ≤ 64` (§12.2). What we add is the integral statement over `ℤ_2`, with explicit lattices.
(2) The proof uses no result of the general theory of tilting modules: only (K), Lemma 3.2, Weyl's theorem on complete reducibility over `ℚ`, and the completeness of `ℤ_2`.

**Lemma 3.7.** For `n ≥ 1`: `m_0(n) = 0`; `m_n(n) = 1`; `m_1(n) = 2^{(n−1)/2}` for odd `n`; `m_2(n) = 2^{(n−2)/2}` for even `n`.

*Proof.* In the rule `V·[λ]` the produced symbols are `[1]`, `[λ + 1]` with `λ` odd (even and `≥ 2`), `[2l + 1]`, and `Φ(·) = [2ν + 1]` (odd): `[0]` is never produced. The symbol `[λ + 1]` is the largest symbol of `V·[λ]`, with coefficient `1`, so `m_n(n) = 1`. The symbol `[2]` is produced only by `V·[1]`, so `m_2(n + 1) = m_1(n)`. The symbol `[1]` is produced by `V·[0]` and by the term `2[2l + 1]` of `V·[2]` (`l = 0`), and by `Φ(V·[l])` only if `V·[l]` contains `[0]`, which never happens; so `m_1(n + 1) = m_0(n) + 2m_2(n) = 2m_2(n)` for `n ≥ 1`, with `m_1(1) = 1`. ∎

### 3.4 The groups of the families

For a family `λ`, an integer `α ≥ 1` and a shift `i ≥ 0`, let `D` be the floor operator of `T(λ)` (floor `(λ − w)/2` on weight `w`) and put
  **`σ^{(α)}_i := F + 2^α(D + i)`,  `X^{(α)}(λ, i) := coker(σ^{(α)}_i on T(λ))`.**
For `α = 1`, `σ^{(1)}_i = F + λ − H + 2i`.

**Theorem 3.8.** For every `n ≥ 1`, **`ℤ_2 ⊕ Syl_2 K(Q_n) ≅ ⊕_λ X^{(1)}(λ, (n − λ)/2)^{m_λ(n)}`.**

*Proof.* Corollary 2.3 and Theorem 3.6. On a summand `T(λ)` of `V^{⊗n}`,
  `σ = F + n − H = F + (λ − H) + (n − λ) = σ^{(1)}_{(n−λ)/2}`. ∎

The cube uses `α = 1`; the fold law (§10) uses `α = 2`. The rest of the paper computes `X^{(α)}(λ, i)`.

## 4. The dance: Theorem D

### 4.1 Payment systems

Let `N` be a lattice graded by floors `0, 1, …, f_{max}`, on which `F` maps floor `f` into floor `f + 1`. A **payment** is a function `π: ℤ_{≥0} → A`; `π(D)` denotes the operator that multiplies floor `f` by `π(f)`. A **payment system of size `r`** on `N` is an operator on `N^{⊕r}`, with slots `1, …, r`, of the form
  `G(x ι_{s'}) = (F + π_{s'}(D)) x ι_{s'} + Σ_{s > s'} K_{ss'}(D) x ι_s`  (`x ∈ N`),
where `ι_s` places an element in slot `s` and the **couplings** `K_{ss'}` are payments. It is **even** if every value of every `π_s` and `K_{ss'}` lies in `2A`. The operator `σ^{(α)}_i` on `T(λ)` (§3.4) is an even payment system of size `1`, with `π(d) = 2^α(i + d)`, because `α ≥ 1`.

### 4.2 The two moves

**Proposition 4.1 (the twist move).** Let `N = Φ(N')` with its floor grading (the floor of `b_e n'` is `2f + e` if `n'` has floor `f`). For an even payment system `G` of size `r` on `N`,
  `coker G ≅ coker(2G')`,
where `G'` is the even payment system of size `r` on `N'` with
  `π'_s(f) = −π_s(2f) π_s(2f + 1)/2`,
  `K'_{us'}(f) = −½ [π_{s'}(2f + 1) K_{us'}(2f) + K_{us'}(2f + 1) π_u(2f) + Σ_{s' < s < u} K_{ss'}(2f + 1) K_{us}(2f)]`.

*Proof.* On `Φ(N')`, `F(b_0 n) = b_1 n` and `F(b_1 n) = 2 b_0 (F n)`. For `n ∈ N'` of floor `f`, the relation `G(b_0 n ι_{s'}) = b_1 n ι_{s'} + π_{s'}(2f) b_0 n ι_{s'} + Σ_{s>s'} K_{ss'}(2f) b_0 n ι_s` has coefficient `1` on `b_1 n ι_{s'}`, and every other term lies in `b_0 ⊗ N'`. Eliminating these relations (one for each `n` and `s'`), we see that `coker G` is the quotient of `(b_0 ⊗ N')^{⊕r}` by the relations `G(b_1 n ι_{s'})`, where every `b_1 x ι_s` is replaced by `−π_s(2f) b_0 x ι_s − Σ_{u>s} K_{us}(2f) b_0 x ι_u`. That relation is
  `2 b_0 (Fn) ι_{s'} − π_{s'}(2f+1) π_{s'}(2f) b_0 n ι_{s'}`
  `− Σ_{u>s'} [π_{s'}(2f+1) K_{us'}(2f) + K_{us'}(2f+1) π_u(2f) + Σ_{s'<s<u} K_{ss'}(2f+1) K_{us}(2f)] b_0 n ι_u`,
which is `2 G'(n ι_{s'})` under `b_0 x ↦ x`. The values of `G'` are halves of products of two elements of `2A`, so they lie in `2A`. ∎

**Proposition 4.2 (the split move).** Let `N = V ⊗ Φ(N')`. For `n ∈ N'` of floor `f` put
  `A_n := b_0 ⊗ b_0 n`,  `B_n := b_0 ⊗ b_1 n − b_1 ⊗ b_0 n`,  `C_n := b_1 ⊗ b_0 n`,  `Dd_n := b_1 ⊗ b_1 n`,
of floors `2f`, `2f + 1`, `2f + 1`, `2f + 2`. They form a basis of `N` over the bases of `N'`, and
  `F A_n = B_n + 2 C_n`,  `F B_n = 2 A_{Fn}`,  `F C_n = Dd_n`,  `F Dd_n = 2 C_{Fn}`.
For an even payment system `G` of size `r` on `N`, `coker G ≅ coker(2G'')`, where `G''` is the even payment system of size `2r` on `N'` with slots `(s, A)`, `(s, C)`, ordered lexicographically with `A` before `C`, and
- `π''_{(s,A)}(f) = −π_s(2f) π_s(2f+1)/2`,  `π''_{(s,C)}(f) = −π_s(2f+1) π_s(2f+2)/2`;
- the couplings `(s', A) → (u, A)` are the formula of Proposition 4.1 at the floors `(2f, 2f + 1)`, and the couplings `(s', C) → (u, C)` are the same formula at `(2f + 1, 2f + 2)`;
- `K''_{(s',C),(s',A)}(f) = −π_{s'}(2f + 1)`,  `K''_{(u,C),(s',A)}(f) = −K_{us'}(2f + 1)` (`u > s'`), and there is no coupling from a slot `C` to a slot `A`.

*Proof.* The formulas for `F` follow from `Δ(F) = F ⊗ 1 + 1 ⊗ F` and §3.1: for instance `F A_n = b_1 ⊗ b_0 n + b_0 ⊗ b_1 n = B_n + 2C_n` and `F B_n = b_1 ⊗ b_1 n + 2 b_0 ⊗ b_0 Fn − b_1 ⊗ b_1 n`. The relations `G(A_n ι_{s'})` and `G(C_n ι_{s'})` have coefficient `1` on `B_n ι_{s'}` and `Dd_n ι_{s'}` respectively; eliminate those vectors. Substituting into `G(B_n ι_{s'})` gives
  `2 A_{Fn} ι_{s'} − π_{s'}(2f+1)π_{s'}(2f) A_n ι_{s'} − Σ_u [coupling of Proposition 4.1 at (2f, 2f+1)] A_n ι_u`
  `− 2π_{s'}(2f+1) C_n ι_{s'} − 2Σ_{u>s'} K_{us'}(2f+1) C_n ι_u`,
and substituting into `G(Dd_n ι_{s'})` gives
  `2 C_{Fn} ι_{s'} − π_{s'}(2f+2)π_{s'}(2f+1) C_n ι_{s'} − Σ_u [coupling of Proposition 4.1 at (2f+1, 2f+2)] C_n ι_u`.
Both are twice the relations of `G''` under `A_x ι_s ↦ x ι_{(s,A)}`, `C_x ι_s ↦ x ι_{(s,C)}`. Evenness is as in Proposition 4.1. ∎

### 4.3 The dance

**Proposition 4.3.** Let `λ + 1 = 2^k + Σ_{t∈I} 2^t`, `α ≥ 1` and `i ≥ 0`. Apply to `σ^{(α)}_i` on `T(λ)` the moves of the binary digits `t = 0, 1, …, k − 1` of `λ + 1`, in this order: a twist move if `t ∉ I`, a split move if `t ∈ I`. After the `k` moves one obtains an even payment system on `T(0)^{⊕ 2^{|I|}} = A^{2^{|I|}}`, that is, a lower triangular matrix `M = M^{(α)}(λ, i)` of size `2^{|I|}`, and
  **`X^{(α)}(λ, i) ≅ ⊕_{a=1}^{k−1} (ℤ/2^a)^{2^{|I| + k − 1 − a}} ⊕ coker(2^k M)`.**

*Proof.* If `λ = 2l + 1`, then `λ + 1` has last digit `0`, `T(λ) = Φ(T(l))` and `l + 1 = (λ + 1)/2`; if `λ = 2l + 2`, then `λ + 1` has last digit `1`, `T(λ) = V ⊗ Φ(T(l))` and `l + 1 = λ/2 = ⌊(λ + 1)/2⌋`. In both cases the floor grading of `T(λ)` (floor `(λ − w)/2` at weight `w`) is the grading of Propositions 4.1–4.2: for instance `b_0 n` has weight `2w + 1` and floor `(2l + 1 − 2w − 1)/2 = l − w = 2f`. So the moves can be applied digit by digit, and `T(0) = A` has the single floor `0`, on which `F = 0`. Each move halves the rank, `rank T(λ) = 2^{k+|I|}`, and turns `coker(2^h G)` into `coker(2^{h+1} G')` plus cyclic factors `ℤ/2^h`, as many as half the rank (the eliminated unit pivots, multiplied by `2^h`): the Smith exponents of `2^h G` are `h`, with multiplicity half the rank, and the exponents of `2G'` raised by `h`. At move `h = 0, 1, …, k − 1` the rank is `2^{k+|I|−h}`; the factors of move `0` are trivial, and move `a ≥ 1` gives `(ℤ/2^a)^{2^{k+|I|−a−1}}`. ∎

We use the notation **`coker(2^k M)`** for the module whose Smith exponents are those of `M` raised by `k` (a zero exponent of `M` gives `ℤ/2^k`, an infinite one stays `ℤ_2`). The **dancers** are the subsets `D ⊆ I`: a split move at the digit `t` splits each slot into a slot `A` and a slot `C`, and the final slot `s` is identified with `D(s) := {t ∈ I : s_t = C}`. We index `M` by dancers, in the o-order. The order in which the moves produce the slots is another linear extension of inclusion (for `I = {0, 1}` it is `∅, {1}, {0}, {0, 1}`); re-indexing does not change the Smith form, and `M` is lower triangular in either order, since `M_{DD'} ≠ 0` only if `D' ⊆ D` (Theorem 4.4).

### 4.4 The final matrix in closed form

Put `π_0(d) := 2^α(i + d)`, `K := 2^k` and `o(Δ) := Σ_{t∈Δ} 2^t`.

**Theorem 4.4 (windows).** Let `q_0 := −1` and `q_{t+1} := q_t^2 − [t ∈ I]·y_t q_t` in `ℤ[y_t : t ∈ I]/(y_t^2 : t ∈ I)`, and let `a_k(Δ)` be the coefficient of `y^Δ := ∏_{t∈Δ} y_t` in `q_k`. Then for dancers `D, D'`:
  `M_{DD'} = −2^{1 − K + o(D∖D')} · a_k(D∖D') · ∏_{d = o_D}^{o_{D'} + K − 1} π_0(d)`  if `D' ⊆ D`,
  `M_{DD'} = 0`  otherwise.
The window `[o_D, o_{D'} + K − 1]` has `K − o(D ∖ D') ≥ 1` elements.

*Proof.* Let `I_{<h} := I ∩ [0, h)`. We show by induction on `h = 0, …, k` that after `h` moves the system has one slot for each `D ⊆ I_{<h}`, couplings only from `D'` to `D ⊋ D'`, and
  `π^{(h)}_D(f) = c^{(h)}_∅ · ∏_{d ∈ W} π_0(d)`, `W = [2^h f + o_D, 2^h f + o_D + 2^h − 1]`,
  `K^{(h)}_{DD'}(f) = c^{(h)}_{D∖D'} · ∏_{d ∈ W} π_0(d)`, `W = [2^h f + o_D, 2^h f + o_{D'} + 2^h − 1]`,
where `c^{(h)} = Σ_Δ c^{(h)}_Δ x^Δ ∈ ℚ[x_t : t ∈ I_{<h}]/(x_t^2)` satisfies `c^{(0)} = 1` and `c^{(h+1)} = −(c^{(h)})^2/2 − [h ∈ I]·x_h c^{(h)}`.
For `h = 0` there is one slot, `π(f) = π_0(f)`, `c = 1`. In the formula of Proposition 4.1, each of the three kinds of terms is a product of the values of `π_0` over two **adjacent** windows of level `h`, whose union is the window of level `h + 1`: for instance `π_{D'}(2f+1) K_{DD'}(2f)` multiplies over `[2^{h+1}f + o_D, 2^{h+1}f + o_{D'} + 2^h − 1]` and `[2^{h+1}f + 2^h + o_{D'}, 2^{h+1}f + o_{D'} + 2^{h+1} − 1]`. So every term is the same monomial, and the coefficient of the pair `(D, D')` is `−½ Σ c_{Δ_1} c_{Δ_2}` over the ordered decompositions `D ∖ D' = Δ_1 ⊔ Δ_2` (the intermediate slot is `U = D' ⊔ Δ_1`; the decompositions with `Δ_1 = ∅` or `Δ_2 = ∅` are the first two terms); this is `−½ [(c^{(h)})^2]_{D∖D'}`, since `x_t^2 = 0`. In a split move at `h ∈ I` the slot `D` gives the slots `D` (from `A`) and `D ∪ {h}` (from `C`), with `o_{D∪{h}} = o_D + 2^h`. In the formulas of Proposition 4.2, the diagonal entries have the windows `[2^{h+1}f + o_D, ⋯ + 2^{h+1} − 1]` and `[2^{h+1}f + o_D + 2^h, ⋯ + 2^{h+1} − 1]`; the coupling `−π_{D'}(2f+1)` from `D'` to `D' ∪ {h}` and the coupling `−K_{DD'}(2f+1)` from `D'` to `D ∪ {h}` have the windows `[2^{h+1}f + o_{D'} + 2^h, 2^{h+1}f + o_{D'} + 2^{h+1} − 1]` and `[2^{h+1}f + o_D + 2^h, 2^{h+1}f + o_{D'} + 2^{h+1} − 1]`, which are the windows of the new pairs. Their coefficients `−c_∅` and `−c_{D∖D'}` are the coefficients of `x_h` and `x_h x^{D∖D'}` in `−x_h c^{(h)}`; the other couplings carry `−½[(c^{(h)})^2]_Δ` with `h ∉ Δ`, and `(c^{(h)})^2` has no `x_h`. This proves the recursion. Put `y_t := 2^{2^t} x_t` and `c^{(h)} = −2^{1 − 2^h} q_h`. Then `c^{(0)} = 1` gives `q_0 = −1`, and
  `c^{(h+1)} = −2^{1 − 2^{h+1}} q_h^2 + [h ∈ I] 2^{1 − 2^h} 2^{−2^h} y_h q_h = −2^{1 − 2^{h+1}} (q_h^2 − [h ∈ I] y_h q_h)`,
so `c^{(k)}_Δ = −2^{1−K} a_k(Δ) 2^{o(Δ)}`. At `h = k` there is only the floor `0`, and `M_{DD'} = K^{(k)}_{DD'}(0)`. ∎

### 4.5 The coefficients: the deficit law

**Lemma 4.5 (deficit law).** `a_k(∅) = 1`, and for `∅ ≠ Δ ⊆ I`,
  **`v_2(a_k(Δ)) = k − |Δ| − min Δ =: δ(Δ)`;**  put `δ(∅) := 0`.

*Proof.* The constant term of `q_t` is `1` for `t ≥ 1`. We prove `v_2(a_t(Δ)) = t − |Δ| − min Δ` for every `t > max Δ`, by induction on `|Δ|` and then on `t`. Let `m := max Δ ∈ I` and `μ := min Δ`. Since `q_m` does not involve `y_m`, the coefficient of `y^Δ` in `q_m^2` is `0` and `a_{m+1}(Δ) = −a_m(Δ ∖ {m})`. This is `±1` if `Δ = {m}` (valuation `0 = (m + 1) − 1 − m`); otherwise it has valuation `m − (|Δ| − 1) − μ` by induction. For `t ≥ m + 1`, the term `y_t q_t` does not contribute to `y^Δ`, and
  `a_{t+1}(Δ) = 2a_t(Δ) + 2Σ a_t(Δ_1) a_t(Δ_2)`,
over the unordered decompositions `Δ = Δ_1 ⊔ Δ_2` into non-empty parts. One of `min Δ_1`, `min Δ_2` is `μ` and the other is `≤ m`, so each cross term has valuation at least `1 + 2t − |Δ| − μ − m`, which exceeds `v_2(2a_t(Δ)) = 1 + t − |Δ| − μ` by `t − m ≥ 1`. ∎

So **`v_2(a_k(Δ))` depends only on `k` and `Δ`**, not on the other digits of `λ + 1`; and `δ` is **strictly subadditive**: `δ(Δ_1) + δ(Δ_2) − δ(Δ_1 ⊔ Δ_2) = k − max(min Δ_1, min Δ_2) ≥ 1` for non-empty disjoint `Δ_1`, `Δ_2`.

> **Theorem D.** For every family `λ`, every `α ≥ 1` and every shift `i ≥ 0`,
>   **`X^{(α)}(λ, i) ≅ ⊕_{a=1}^{k−1} (ℤ/2^a)^{2^{|I|+k−1−a}} ⊕ coker(2^k M^{(α)}(λ, i))`,**
> with `M^{(α)}(λ, i)` the explicit integer matrix of Theorem 4.4, whose entries have the valuations
>   **`v_2(M_{DD'}) = 1 − K + o(D∖D') + δ(D ∖ D') + Σ_{d=o_D}^{o_{D'}+K−1} (α + v_2(i + d))`**  (`D' ⊆ D`).
> Hence, by Theorem 3.8, `ℤ_2 ⊕ Syl_2 K(Q_n)` is the direct sum, over the families `λ`, of `m_λ(n)` copies of the small clocks and of `coker(2^k M^{(1)}(λ, (n − λ)/2))`.

*Proof.* Proposition 4.3, Theorem 4.4 and Lemma 4.5. ∎

**Example.** `λ = 6` (`k = 2`, `I = {0, 1}`): `q_1 = 1 + y_0`, `q_2 = 1 + 2y_0 − y_1 − y_0 y_1`. With `p_d := π_0(d)`, `M = −(1/8)·A`, where `A` is, in the o-order (row `D`, column `D'`):

| `D` \ `D'` | `∅` | `{0}` | `{1}` | `{0,1}` |
|---|---|---|---|---|
| `∅` | `p_0p_1p_2p_3` | `0` | `0` | `0` |
| `{0}` | `4p_1p_2p_3` | `p_1p_2p_3p_4` | `0` | `0` |
| `{1}` | `−4p_2p_3` | `0` | `p_2p_3p_4p_5` | `0` |
| `{0,1}` | `−8p_3` | `−4p_3p_4` | `4p_3p_4p_5` | `p_3p_4p_5p_6` |

The matrix `M` has `2^{|I|} ≤ ⌊λ/2⌋ + 1` rows (with equality, for instance, when `λ = 2^{k+1} − 2`), against `2^n` for the Laplacian and `2^{k+|I|} = dim T(λ)` for the family; its entries are closed forms. What remains is its Smith form.

## 5. The valuations: rulers, gold and clocks

Fix a family `λ` (`λ + 1 = 2^k + Σ_{t∈I} 2^t`, `K = 2^k`), `α ≥ 1`, and a shift `i ≥ 1`; put `m := i − 1`. For `t ∈ I` recall `h_t = next(t) − t ≥ 1`. Let `t_1 := min I` (`t_1 := k` if `I = ∅`). For dancers `a ⊇ b` write `Δ := a ∖ b`.

**Definitions.** For `μ ≥ 0` and `E ⊆ I`, the **ruler**
  `R_μ(E) := Σ_{t∈E} (h_t − α 2^t) − κ(μ, o_E)`;
the **gold** of `Δ ⊆ I`,
  `γ(Δ) := Σ_{u ∈ I∖Δ, u > min Δ} h_u`  (`γ(∅) := 0`),
the gaps of `I` above `min Δ` that `Δ` skips; and the **clocks of the cell**
  `x_D := R_m(D) − R_{m+K}(I ∖ D)`.
For `α = 1` this is the definition of §1.2.

**Lemma 5.1.** (a) `δ(Δ) = Σ_{t∈Δ}(h_t − 1) + γ(Δ)`. (b) `γ(Δ) = 0` if and only if `Δ = ∅` or `Δ = I ∩ [min Δ, k)` (a **tail** of `I`).

*Proof.* (a) `k − min Δ = Σ_{t ∈ I, t ≥ min Δ} h_t` (the gaps telescope), and the digits `t ≥ min Δ` of `I` are those of `Δ` and those counted in `γ(Δ)`. (b) Each `h_u ≥ 1`. ∎

**Proposition 5.2 (the cost form).** For dancers `b ⊆ a`,
  **`v_2(M^{(α)}(λ, i)_{ab}) = αK + κ(m, K) + R_m(a) − R_{m+K}(b) + γ(a ∖ b)`.**

*Proof.* By Theorem D, `v_2(M_{ab}) = 1 − K + o(Δ) + δ(Δ) + α(K + o_b − o_a) + Σ_{d=o_a}^{o_b+K−1} v_2(i + d)`. By Legendre's formula `v_2(x!) = x − s_2(x)`, `Σ_{d=x}^{y−1} v_2(m + 1 + d) = (y − x) − s_2(m + y) + s_2(m + x)`. With `x = o_a`, `y = o_b + K` and `o(Δ) = o_a − o_b`:
  `v_2(M_{ab}) = 1 + δ(Δ) + α(K + o_b − o_a) − s_2(m + K + o_b) + s_2(m + o_a)`.
By Lemma 5.1(a), `δ(Δ) = G(a) − G(b) + γ(Δ)` with `G(E) := Σ_{t∈E}(h_t − 1)`. Since `κ(μ, o_E) = s_2(μ) + |E| − s_2(μ + o_E)`, we have
  `R_μ(E) = G(E) − α o_E + s_2(μ + o_E) − s_2(μ)`.
Substituting,
  `v_2(M_{ab}) − [R_m(a) − R_{m+K}(b) + γ(Δ)] = 1 + αK + s_2(m) − s_2(m + K) = αK + κ(m, K)`,
because `s_2(K) = 1`. ∎

So every entry of `M` is a constant of the cell, plus a **row term** read from the carries of `m + o_a`, minus a **column term** read from the carries of `m + K + o_b`, plus the gold of the arrow. We write
  `ĉ(a, b) := R_m(a) − R_{m+K}(b) + γ(a ∖ b)`  (`b ⊆ a`)
for the **normalized cost** of the arrow `a → b`.

**Proposition 5.3 (the clocks of §1.2).** For `α = 1`, every family `λ`, every `i ≥ 1` and every dancer `D`,
  **`u_i(D) = k + K + κ(m, K) + x_D`.**

*Proof.* Put `E := I ∖ D` and `ξ := ξ_D = λ + 1 − 2o_D = K + o_E − o_D`, so `o_D + ξ = K + o_E`.
*Step 1 (`i = 1`).* We show
  `u_1(D) = φ(λ + 1) + 2ψ(D)`,  with  `ψ(D) := Σ_{t∈D}(h_t − 2^t)`.
Let `μ := ξ − 1 = λ − 2o_D`. Since `K − 1 = o([0, k) ∖ I) + o_I`, we have `μ = o([0, k) ∖ I) + 2o_E`. Adding `2^{t+1}` (`t ∈ E`) to `o([0, k) ∖ I)` carries through the positions `t + 1, …, next(t) − 1`, which lie in `[0, k) ∖ I`, and stops at `next(t)`, a position that is set neither in `o([0, k) ∖ I)` nor by any other `t`; the stretches `[t + 1, next(t)]` of different `t` are disjoint. Hence `s_2(μ) = (k − |I|) + |E| − G(E)`. Now `φ(ξ) = ξ + v_2(ξ)` and `s_2(ξ) = s_2(μ) + 1 − v_2(ξ)`, and `κ(o_D, ξ) = |D| + s_2(ξ) − s_2(K + o_E) = |D| + s_2(ξ) − 1 − |E|`. So
  `u_1(D) = ξ + v_2(ξ) + s_2(ξ) − 1 + |D| − |E| + h(D) = ξ + s_2(μ) + |D| − |E| + h(D)`
  `= K + o_I − 2o_D + k − |I| + 2|D| + G(D) − G(E)`,
using `ξ = K + o_I − 2o_D` and `h(D) = G(D) + |D|`. On the other side
  `φ(λ + 1) = K + o_I + t_1`,  `2ψ(D) = 2G(D) + 2|D| − 2o_D`.
The difference of the two sides is `k − |I| − G(D) − G(E) − t_1 = k − t_1 − Σ_{t∈I} h_t = 0`.
*Step 2 (`i ≥ 1`).* From `κ(a, b) = s_2(a) + s_2(b) − s_2(a + b)`, `κ(m + o_D, ξ) − κ(o_D, ξ) = κ(m, o_D + ξ) − κ(m, o_D)`, so
  `u_i(D) = u_1(D) + κ(m, K + o_E) − κ(m, o_D)`.
*Step 3.* `x_D = ψ(D) − κ(m, o_D) − ψ(E) + κ(m + K, o_E)`, and
  `κ(m, K + o_E) + κ(K, o_E) = κ(m, K) + κ(m + K, o_E)`
(both sides are `s_2(m) + s_2(K) + s_2(o_E) − s_2(m + K + o_E)`), with `κ(K, o_E) = 0`. Hence `u_i(D) − k − K − κ(m, K) − x_D = φ(λ + 1) + ψ(D) + ψ(E) − k − K = φ(λ + 1) + ψ(I) − k − K`, and `ψ(I) = (k − t_1) − o_I`, so this is `0`. ∎

**The shift `i = 0`.** Here the payment `π_0(0) = 0` makes the row `∅` of `M(λ, 0)` zero (its window `[0, K − 1]` contains `d = 0`), and no other window contains `0`. The same computation with Legendre's formula at `i = 0`, `Σ_{d=x}^{y−1} v_2(d) = (y − x) − s_2(y − 1) + s_2(x − 1)` (`x ≥ 1`), is the case «`m = −1`»: since `m + K + o_b = K − 1 + o_b`, both rulers are read at `K − 1` (Proposition 5.4). In the language of §7.3 this is the house with `ℓ = K − 1`.

**Proposition 5.4.** For `D ≠ ∅` and every `b ⊆ D`,
  `v_2(M(λ, 0)_{Db}) = αK + R^♯(D) − R^♯(b) + γ(D ∖ b)`,  `R^♯(E) := Σ_{t∈E}(h_t − α 2^t) − κ(K − 1, o_E)`,
and, for `α = 1`, `u_0(D) = k + K + x^♯_D` with `x^♯_D := R^♯(D) − R^♯(I ∖ D)`. Explicitly `κ(K − 1, o_E) = k − min E` (with `min ∅ := k`).

*Proof.* Let `E ≠ ∅`. Then `K − 1 + o_E = K + (o_E − 1)` and `s_2(o_E − 1) = |E| − 1 + min E`, so that `κ(K − 1, o_E) = k + |E| − 1 − s_2(o_E − 1) = k − min E`; for `E = ∅` both sides are `0`. As in Proposition 5.2, `R^♯(E) = G(E) − α o_E + s_2(K − 1 + o_E) − k`, and, for `D ≠ ∅`, `s_2(K − 1 + o_D) = 1 + s_2(o_D − 1)`. Legendre's formula, applied at `i = 0` with `x = o_D ≥ 1` and `y = o_b + K`, gives
  `v_2(M_{Db}) = 1 + δ(Δ) + α(K + o_b − o_D) − s_2(K − 1 + o_b) + s_2(o_D − 1)`,
and with `δ(Δ) = G(D) − G(b) + γ(Δ)` the difference `v_2(M_{Db}) − [R^♯(D) − R^♯(b) + γ(Δ)]` is `αK`. For the clocks: in `u_i(D)` the first argument of `κ` is `i + o_D − 1`, which is `o_D − 1` at `i = 0` against `o_D` at `i = 1`, while `ξ` is unchanged; and `κ(o_D − 1, ξ) − κ(o_D, ξ) = v_2(o_D) − v_2(o_D + ξ) = min D − min E` (`v_2(K + o_E) = min E`). So `u_0(D) = u_1(D) + min D − min E = k + K + ψ(D) − ψ(E) + min D − min E`, and `x^♯_D = ψ(D) − (k − min D) − ψ(E) + (k − min E)` is the same. ∎

## 6. The Smith form of `M`: the ceiling

### 6.1 Determinantal divisors and the tropical bound

For a matrix `M` over `A` with Smith exponents `e_1 ≤ e_2 ≤ ⋯`, the `r`-th **determinantal divisor** `d_r(M)`, the least valuation of an `r × r` minor, is `e_1 + ⋯ + e_r`. So `r ↦ d_r` is convex with integer increments, and the increments are the exponents.

Fix a cell `(λ, i, α)` with `i ≥ 1`, and number the dancers in o-order, `D_0 = ∅, D_1, …, D_{N−1} = I` (`N = 2^{|I|}`). Since `o_{I∖D} = o_I − o_D`, the map `D ↦ I ∖ D` reverses the o-order. Put `L_r := {D_{N−r}, …, D_{N−1}}` (the last `r` dancers) and `F_r := {D_0, …, D_{r−1}} = {I ∖ D : D ∈ L_r}` (the first `r`). Write
- `d̂_r := d_r(M) − r(αK + κ(m, K))` (the normalized divisors);
- `T(r)` := the least normalized cost `Σ ĉ(a, β(a))` of an **`r`-matching**: a bijection `β` from `r` dancers onto `r` dancers with `β(a) ⊆ a` for every `a`;
- `U(r) := Σ_{D∈L_r} x_D`, the sum of the last `r` clocks (the **natural** partial sums);
- `Y(r) := Σ_{D∈L_r} ŷ_D`, the same for the integer antitonic fit `ŷ` of `x` (the **pooled** partial sums).

**Lemma 6.1 (tropical bound).** `d̂_r ≥ T(r)`.

*Proof.* An `r × r` minor is a signed sum of products of `r` entries along a bijection from its rows to its columns. A product is non-zero only if every entry lies in the support `{b ⊆ a}` of `M`, and then its normalized valuation is the cost of the matching (Proposition 5.2). ∎

### 6.2 Theorem O: the unique golden matching

Call an arrow `a → b` (`b ⊆ a`) **golden** if `γ(a ∖ b) = 0`, that is (Lemma 5.1(b)), if `b = a` or `b = a ∖ T` for a tail `T = I ∩ [t, k)` of `I` contained in `a`.

**Theorem 6.2 (Theorem O).** For every `I ⊆ [0, k)` and every `0 ≤ r ≤ N`, there is **exactly one** bijection `β_r: L_r → F_r` all of whose arrows `D → β_r(D)` are golden.

*Proof.* Let `t_1 < ⋯ < t_s` be the digits of `I` and identify a dancer `D` with the integer `p(D) := Σ_j [t_j ∈ D] 2^{j−1} ∈ [0, 2^s)`; the o-order is the order of `p`. A tail of `I` contained in `D` is a set of top bits of `p(D)` that are all equal to `1`, so the golden images of `p` are `p` itself and the numbers obtained from `p` by clearing a non-empty block of its top bits, all equal to `1`. We must show that there is exactly one bijection from `{N − r, …, N − 1}` onto `{0, …, r − 1}` that sends every `p` to a golden image. Induction on `s`; `s = 0` is trivial. Let `N = 2^s ≥ 2`.
- `r ≤ N/2`: every row has top bit `1` and every column has top bit `0`, so every arrow clears the top bit, followed by a golden arrow of the remaining `s − 1` bits. Removing the top bit of the rows gives exactly the problem `(s − 1, r)`, which has one solution.
- `r = N/2 + q` with `0 < q ≤ N/2`: the columns `N/2, …, N/2 + q − 1` have top bit `1` and are reached only by loops, so they are matched with themselves, and they are rows. The rows `N/2 − q, …, N/2 − 1` have top bit `0` and admit only loops, so they are matched with themselves, and they are columns. The remaining rows `N/2 + q, …, N − 1` must go to the remaining columns `0, …, N/2 − q − 1` by clearing the top bit: this is the problem `(s − 1, N/2 − q)`, which has one solution. ∎

The golden matching is explicit: for `r ≤ N/2` it is «remove the top digit of `I` and solve the smaller problem», and for `r > N/2` it fixes the `2r − N` middle dancers and solves the smaller problem on the rest.

**Corollary 6.3 (the natural minor).** `v_2(det M[L_r, F_r]) = r(αK + κ(m, K)) + U(r)`; hence `d̂_r ≤ U(r)` for every `r`.

*Proof.* For a bijection `β: L_r → F_r` inside the support, the normalized valuation of its term is
  `Σ_{D∈L_r} R_m(D) − Σ_{E∈F_r} R_{m+K}(E) + Σ_D γ(D ∖ β(D))`.
The first two sums do not depend on `β` and add up to `Σ_{D∈L_r}(R_m(D) − R_{m+K}(I ∖ D)) = U(r)`. The gold is a non-negative integer, zero exactly for the golden matching `β_r`. So the minor has a unique term of least valuation, and its valuation is that of the term. ∎

### 6.3 From the natural sums to the pooled sums

**Lemma 6.4 (convexity).** Let `d: {0, …, N} → ℤ` be convex with integer increments, `d(0) = 0`, and `d(r) ≤ U(r)` for every `r`. Then `d(r) ≤ Y(r)` for every `r`.

*Proof.* Read the dancers from the end. On every level set of the real antitonic fit (§7.1) the sums of `x` and of `ŷ` agree, so `Y = U` at the two ends `r_0 < r_1 = r_0 + p` of each level set, counted from the end. Inside a level set with sum `S = pq + ρ` (`0 ≤ ρ < p`), `Y` increases by `q` on the first `p − ρ` steps and by `q + 1` on the last `ρ` steps (the fit takes the larger values first in o-order). We argue by induction over the level sets from the end, so we may assume `d(r_0) ≤ Y(r_0)`. Suppose `d(r^*) > Y(r^*)` with `r_0 < r^* < r_1`.
- If `r^* ≤ r_0 + p − ρ`, some increment of `d` in `(r_0, r^*]` is at least `q + 1`, hence so is every later one, and `d(r_1) ≥ d(r^*) + (r_1 − r^*)(q + 1) > Y(r^*) + (r_1 − r^*)(q + 1) ≥ Y(r_1) = U(r_1)`, a contradiction.
- If `r^* > r_0 + p − ρ`, then `d(r_1) − d(r^*) < Y(r_1) − Y(r^*) = (r_1 − r^*)(q + 1)`, so some increment of `d` in `(r^*, r_1]` is at most `q` (they are integers), hence so is every earlier one, and `d(r^*) ≤ d(r_0) + (r^* − r_0)q ≤ Y(r^*)`, a contradiction. ∎

**Theorem 6.5.** Suppose `T(r) ≥ Y(r)` for every `r` and that the integer fit `ŷ` is non-increasing. Then `d̂_r = Y(r)` for every `r`, and the Smith exponents of `M^{(α)}(λ, i)` are `αK + κ(m, K) + ŷ_D`, `D ⊆ I`.

*Proof.* `Y(r) ≤ T(r) ≤ d̂_r ≤ Y(r)`, by the hypothesis, Lemma 6.1, and Corollary 6.3 with Lemma 6.4 (applied to `d̂`). Since `ŷ` is non-increasing, `Y(r)` is the sum of the `r` smallest values of `ŷ`, and the exponents are the increments. ∎

The two hypotheses are proved in §7 (Theorem 7.8 and Lemma 7.9).

## 7. The Smith form of `M`: the floor

### 7.1 Antitonic fits

For a real sequence `x = (x_0, …, x_{N−1})`, its **antitonic fit** `z = fit(x)` is the non-increasing sequence nearest to `x` in the Euclidean norm; it exists and is unique (projection onto a closed convex cone). Its **level sets** are the maximal runs of positions with equal value. The **integer fit** replaces, on each level set of `p` positions with sum `S` (necessarily `S = p·z`), the values by `S mod p` copies of `⌈S/p⌉` followed by `p − (S mod p)` copies of `⌊S/p⌋`; this is the integer antitonic fit of §1.2, computed there by the pool-adjacent-violators algorithm [ABERS55], [BBBB72].

**Lemma 7.1 (characterization).** A non-increasing sequence `z` is `fit(x)` if and only if, for every level set `[p, q]` of `z`, `Σ_{j=p}^{q}(x_j − z_j) = 0` and `Σ_{j=p}^{s}(x_j − z_j) ≤ 0` for `p ≤ s ≤ q`.

*Proof.* If a prefix of a level set had a positive sum, raising the values on that prefix by a small `ε` and lowering the rest of the level set would keep `z` non-increasing and decrease the distance; the same with a non-zero total. Conversely, let `y` be non-increasing. Then `‖x − y‖^2 = ‖x − z‖^2 + ‖z − y‖^2 + 2Σ_j (x_j − z_j)(z_j − y_j)`, and on a level set `[p, q]` with value `c`, Abel summation with `S_s := Σ_{j=p}^{s}(x_j − c) ≤ 0` (`S_q = 0`) gives
  `Σ_{j=p}^{q}(x_j − c)(c − y_j) = −Σ_{s=p}^{q−1} S_s (y_s − y_{s+1}) ≥ 0`,
since `y` is non-increasing. So `‖x − y‖ ≥ ‖x − z‖`. ∎

We say that `x` is **cut** at a position `b` (`0 < b < N`) if `fit(x)` is the concatenation of `fit(x_{<b})` and `fit(x_{≥b})`. The cut is **strict** if moreover `fit(x)_{b−1} > fit(x)_b`. A position `b` with `fit(x)_{b−1} > fit(x)_b` is always a cut, since Lemma 7.1 is a condition on each level set separately and so holds for the two pieces; thus `b` is a strict cut if and only if no level set of `fit(x)` contains both `b − 1` and `b`.

**Lemma 7.2 (cuts and shifts).**
(a) If `fit(x_{<b})` followed by `fit(x_{≥b})` is non-increasing, then `x` is cut at `b`.
(b) Let `x` be cut at the positions `b_1 < ⋯ < b_s`, and let `δ` be a non-increasing sequence that is constant between consecutive cut positions. Then `fit(x + δ) = fit(x) + δ`, and `x + δ` is cut at the same positions. If moreover `δ` is integer and constant on every level set of `fit(x)` — in particular, if every position at which `δ` changes is a strict cut of `x` — then `fit(x + δ)` has the level sets of `fit(x)`, the strict cuts of `x` are strict cuts of `x + δ`, and the integer fit of `x + δ` is the integer fit of `x` plus `δ`.
(c) If `fit(x)_{<b} = fit(x_{<b})`, or `fit(x)_{≥b} = fit(x_{≥b})`, then `x` is cut at `b`.

*Proof.* (a) Each level set of the concatenation is a level set of one piece, or the union of a final level set of the first piece and an initial one of the second with the same value; Lemma 7.1 for the pieces gives it for the union (a prefix that crosses the cut has the total `0` of the first part plus a prefix sum `≤ 0`). (b) On each piece the fit of `x + const` is the fit plus the constant; the concatenation is non-increasing, so (a) applies. Now let `δ` be integer and constant on every level set. Two adjacent level sets of `fit(x)`, with values `μ_A > μ_B`, receive constants `δ_A ≥ δ_B`, so `μ_A + δ_A > μ_B + δ_B`: the level sets of `fit(x) + δ` are those of `fit(x)`, and a strict cut stays strict (a strict drop of the fit is a cut). On a level set of `p` positions with sum `S`, adding the integer `δ_L` to every position adds `pδ_L` to the sum, keeps `S mod p`, and adds `δ_L` to `⌈S/p⌉` and to `⌊S/p⌋`; so the integer fit is shifted by `δ`. A level set never contains the two sides of a strict cut, so a `δ` that changes only at strict cuts is constant on every level set. Without this hypothesis the integer claim fails: `x = (3, 4, 3, 4)` is cut at `2` but not strictly (`fit(x) = (7/2, 7/2, 7/2, 7/2)`), and for `δ = (1, 1, 0, 0)` the integer fit of `x + δ` is `(5, 4, 4, 3)`, while the integer fit of `x` plus `δ` is `(4, 4, 3, 3) + δ = (5, 5, 3, 3)`. (c) Suppose `z := fit(x)` agrees with `fit(x_{<b})` before `b`. Let `L = L_1 ∪ L_2` be a level set of `z`, with value `c`, that crosses `b` (`L_1` before `b`). The set `L_1` is a final level set of `fit(x_{<b})`, so `Σ_{L_1}(x − c) = 0`; hence the sum of `x − c` over a prefix of `L_2` equals its sum over `L_1` plus that prefix, which is `≤ 0` by Lemma 7.1 for `z`, and the total over `L_2` is `0`. The level sets of `z` after `b` are unchanged, so `z_{≥b}` satisfies Lemma 7.1 for `x_{≥b}`. The second hypothesis is the first one for the reversed and negated sequence. ∎

**Antisymmetry.** For dancers in o-order, the **mirror** is `D ↦ I ∖ D`, the reversal of positions; `x` is **antisymmetric** if `x_{I∖D} = −x_D`. The fit of an antisymmetric sequence is antisymmetric, and so is its integer fit (on a level set of size `p` and sum `−S` the rule gives `p − (S mod p)` copies of `−⌊S/p⌋` followed by `−⌈S/p⌉`); hence a position `b` is a cut if and only if its mirror `N − b` is, and a strict cut if and only if its mirror is.

**Lemma 7.3 (antisymmetric gluing).** Let `x` be antisymmetric of length `2N'`, let `Z_1 = fit(x_{<N'})` and let `X_1` be the integer fit of `x_{<N'}`. Then
  **`fit(x) = [max(Z_1, 0), min(Z_2, 0)]`** and the integer fit of `x` is **`[max(X_1, 0), min(X_2, 0)]`**,
where `Z_2`, `X_2` are the mirror-negatives of `Z_1`, `X_1` (so `Z_2 = fit(x_{≥N'})`).

*Proof.* The candidate `z` is non-increasing. Its level sets are the level sets of `Z_1` with positive value, their mirrors, and one **central** level set `P ∪ P^*` with value `0`, where `P = {Z_1 ≤ 0}` is a final segment of the first half, a union of level sets of `Z_1`, and `P^*` is its mirror. The positive level sets satisfy Lemma 7.1 because they do for `Z_1`; their mirrors by antisymmetry. On `P ∪ P^*` the total of `x` is `0` by antisymmetry. A prefix contained in `P` has sum at most the corresponding sum of `Z_1`, by Lemma 7.1 applied to the level sets of `Z_1` that it covers, and that sum is `≤ 0`. A prefix that covers `P` and the first `L` positions of `P^*` has sum `Σ_P x − Σ_{last L positions of P} x`, the sum over the first `|P| − L` positions of `P`, which is `≤ 0` again. So `z = fit(x)`. The integer fit takes on the positive level sets the same values as `X_1`, and `0` on the central one; and `X_1 ≥ 0` where `Z_1 > 0`, `X_1 ≤ 0` where `Z_1 ≤ 0`. ∎

### 7.2 Theorem U

**Theorem 7.4 (Theorem U).** Let a cell have costs `ĉ(a, b)` on its arrows and pooled clocks `ŷ`. Suppose there are real functions `v` («rows») and `w` («columns») on the dancers such that
- (U1) `v` and `w` are non-increasing in o-order;
- (U2) `v(D) − w(I ∖ D) = ŷ_D` for every dancer `D`;
- (U3) `v(a) − w(b) ≤ ĉ(a, b)` for every arrow `b ⊆ a` (loops included).

Then every `r`-matching costs at least `Y(r) = Σ_{D∈L_r} ŷ_D`; that is, `T(r) ≥ Y(r)`.

*Proof.* For an `r`-matching with rows `R` and columns `C`, by (U3) its cost is at least `Σ_R v − Σ_C w`. By (U1), `Σ_R v ≥ Σ_{L_r} v` and `Σ_C w ≤ Σ_{F_r} w`. Since `F_r = {I ∖ D : D ∈ L_r}`, (U2) gives `Σ_{L_r} v − Σ_{F_r} w = Σ_{L_r} ŷ`. ∎

### 7.3 Houses, windows and penalties

A **house** is `H = (I, k, ℓ, α)` with `I ⊆ [0, k)`, `0 ≤ ℓ < 2^k` and `α ≥ 1`. Its **base ruler**, **carry-out set**, **base clocks** and **base costs** are
  `R_H(E) := Σ_{t∈E} (h_t − α2^t) − κ(ℓ, o_E)`,  `J_H(E) := [ℓ + o_E ≥ 2^k]`,
  `x_H(D) := R_H(D) − R_H(I ∖ D)`,  `ĉ_H(a, b) := R_H(a) − R_H(b) + γ(a ∖ b)`.
The sequence `x_H` is antisymmetric, and `J_H` is an up-set of the o-order (it is monotone in `o_E`). For integers `P_r, P_c ≥ 0` the **penalty cell** `Cell(H; P_r, P_c)` has the costs `ĉ_H(a, b) − P_r J_H(a) + P_c J_H(b)` and the clocks `x_H(D) − P_r J_H(D) + P_c J_H(I ∖ D)`.

For `μ ≥ 0` let `r_k(μ)` be the number of consecutive ones of `μ` starting at bit `k`, that is `r_k(μ) = v_2(⌊μ/2^k⌋ + 1)`.

**Lemma 7.5 (real cells).** Let `i ≥ 1`, `m = i − 1` and `ℓ := m mod K`, and let `H = (I, k, ℓ, α)`. Then `R_m = R_H − r_k(m) J_H` and `R_{m+K} = R_H − r_k(m + K) J_H`; so the cell `(λ, i, α)` is `Cell(H; r_k(m), r_k(m + K))`.

*Proof.* In the sum `m + o_E` the low part `ℓ + o_E` produces the carries of `κ(ℓ, o_E)`, and a carry out of bit `k − 1` exactly when `J_H(E) = 1`; that carry then runs through the `r_k(m)` ones of `m` that start at bit `k`. The same holds for `m + K`, whose low part is also `ℓ`. (One of the two penalties is `0`: the bit `k` is `1` in exactly one of `m` and `m + K`.) ∎

**Windows.** For `t ∈ I` let `W_t := [t, next(t))`, of length `h_t`. The **type** of `t` is the bit `T_t` of `ℓ` at position `t`. Let `r_u(ℓ)` be the number of consecutive ones of `ℓ` starting at bit `u`, and put
  `κ_t := min(r_t(ℓ), h_t)` if `T_t = 1`,  `κ_t := 1 + min(r_{t+1}(ℓ), h_t − 1)` if `T_t = 0`;
  `sat_t := [κ_t = h_t]` (the window is **saturated** if `sat_t = 1`),  `τ_t := h_t − α2^t − [T_t = 1] κ_t`.

**Lemma 7.6 (the gates).** For `E ⊆ I`, let `c_t(E) ∈ {0, 1}` be the carry into bit `t` in the sum `ℓ + o_E`, and `d = [t ∈ E]`. Then `c_{t_1}(E) = 0` and:
- if `T_t = 1`, the window `W_t` makes `κ_t` carries if `d ∨ c_t`, and none otherwise;
- if `T_t = 0`, it makes `κ_t` carries if `d ∧ c_t`, and none otherwise;
- a carry leaves `W_t` (`c_{next(t)} = 1`) if and only if the window makes carries and is saturated.

Hence `R_H(E) = Σ_{t∈E} τ_t − Σ_{t∈I} κ_t c_t(E)·[(T_t = 1 ∧ t ∉ E) ∨ (T_t = 0 ∧ t ∈ E)]`, and `J_H(E) = c_k(E)`.

*Proof.* Inside `W_t` the addend `o_E` has at most the bit `t`, and `ℓ` has the bit `T_t` at `t`. If `T_t = 1` and `d + c_t ≥ 1`, bit `t` carries, and the carry runs through the ones of `ℓ` at `t + 1, …`: there are `min(r_t(ℓ), h_t)` carries inside the window (for `d + c_t = 2` the carry out of bit `t` is the same and the run starts at `t + 1`, which gives the same count). If `T_t = 0`, bit `t` carries only when `d = c_t = 1`, and then the carry runs through the `r_{t+1}(ℓ)` ones above `t`. The carry leaves the window exactly when all its positions carry. Below `t_1` the addend is zero, so no carry is born there. Finally, `κ(ℓ, o_E) = Σ_t (carries in W_t)` and `Σ_{t∈E} κ_t [T_t = 1]` is absorbed into `τ`. ∎

**Lemma 7.7 (the top digit).** Let `I ≠ ∅`, `c := max I`, `I' := I ∖ {c}`, `H' := (I', c, ℓ mod 2^c, α)`, and let `T, κ, sat, τ` be the data of the window `W_c = [c, k)` of `H`, of length `h := k − c`. For `D_0 ⊆ I'`:
  `R_H(D_0) = R_{H'}(D_0) − [T = 1] κ J_{H'}(D_0)`,  `R_H(D_0 ∪ {c}) = τ + R_{H'}(D_0) − [T = 0] κ J_{H'}(D_0)`,
  `J_H(D_0) = [T = 1]·sat·J_{H'}(D_0)`,  `J_H(D_0 ∪ {c}) = sat·([T = 1] + [T = 0] J_{H'}(D_0))`,
and for `Δ ⊆ I`: `γ_I(Δ) = γ_{I'}(Δ) + h` if `c ∉ Δ ≠ ∅`, and `γ_I(Δ_0 ∪ {c}) = γ_{I'}(Δ_0)`. Consequently the first half of the base clocks of `H` (the dancers without `c`) is `x_{H'} + d_1`, with
  `d_1(D_0) := −τ − [T = 1] κ J_{H'}(D_0) + [T = 0] κ J_{H'}(I' ∖ D_0)`,
and the second half is its mirror-negative.

*Proof.* The windows of the digits of `I'` are the same in `H` and in `H'` (the predecessor of `c` has `next = c` in both), with the same types and data; the carry into `W_c` is `c_c(E) = J_{H'}(E ∩ I')`. Apply Lemma 7.6 to `H` and to `H'`. For `γ`: the digit `c` is skipped by every non-empty `Δ ∌ c`, and is never skipped otherwise. The clocks follow by subtraction, with `I ∖ D_0 = (I' ∖ D_0) ∪ {c}`. ∎

### 7.4 Theorem F

**Theorem 7.8 (Theorem F, the floor).** For every house `H = (I, k, ℓ, α)`, let `ŷ_H` be the integer fit of `x_H`. There is a function `V: 2^I → ℤ` with
- (E) `V(D) − V(I ∖ D) = ŷ_H(D)` for every `D`;
- (M) `V` non-increasing in o-order;
- (G) `V(a) − V(b) ≤ ĉ_H(a, b)` for every `b ⊊ a`;

and moreover:
- (Cut) `x_H` is cut at the first dancer `b` with `J_H(b) = 1` (if any), and hence at its mirror; and these cuts are **strict**: `fit(x_H)` is larger at the dancer before `b` than at `b`, and likewise at the mirror. (`b ≠ ∅`, since `J_H(∅) = [ℓ ≥ 2^k] = 0`.)
- (Λ) `|ŷ_H| ≤ α(2^k − 1)`.

*Proof.* Induction on `|I|`. For `I = ∅` there is one dancer, `x = ŷ = 0`, `V := 0`, and `J_H(∅) = [ℓ ≥ 2^k] = 0`. Let `I ≠ ∅` and let `H'`, `c`, `T`, `κ`, `sat`, `τ`, `h` be as in Lemma 7.7, with `V'`, `ŷ'`, `J'` given by the induction hypothesis for `H'`. Write `X_1 := ŷ' + d_1` on the dancers `D_0 ⊆ I'` and `X_2` for its mirror-negative.

1. **The walk.** The sequence `d_1` is integer, non-increasing, and changes only at the first dancer with `J' = 1` and at its mirror (`J'` is an up-set; `J' ∘ mirror` is a down-set). These are strict cuts of `x_{H'}`, by (Cut) for `H'`. So, by Lemma 7.2(b), the real fit of `x_{H'} + d_1` is `fit(x_{H'}) + d_1`, with the level sets of `fit(x_{H'})`, and its integer fit is `X_1`. By Lemma 7.3,
   **`ŷ_H = [max(X_1, 0), min(X_2, 0)]`.**
2. **(Λ).** `d_1 ≤ −τ + [T = 0]κ = α2^c − h + κ ≤ α2^c`, since `κ ≤ h`. With (Λ) for `H'`, `X_1 ≤ α(2^c − 1) + α2^c ≤ α(2^k − 1)`; so `0 ≤ max(X_1, 0) ≤ α(2^k − 1)`, and the second half follows by antisymmetry.
3. **(Cut).** By Lemma 7.7, `J_H = [T = 1]·sat·(J', 1)`, or `sat·[T = 0]·(0, J')`, or `J_H ≡ 0` (we write a function on `2^I` as the pair of its values on the two halves).
   (a) `T = 1`, `sat = 1`, `J' ≢ 0`: the boundary `b` of `J_H` is the boundary of `J'` in the first half. Saturation of type `1` means `κ = h`, so `τ = −α2^c` and `d_1 = α2^c − hJ'`. Just before `b`, `J' = 0` and `X_1 = ŷ' + α2^c ≥ α > 0` by (Λ) for `H'`; so the real fit `Z_1` of the first half is positive before `b`, and by Lemma 7.3 `fit(x_H)_{<b} = (Z_1)_{<b}`. The first half is cut at `b` (step 1), so `(Z_1)_{<b} = fit((x_H)_{<b})`, and Lemma 7.2(c) gives the cut. It is strict: on the first half `fit(x_H) = max(Z_1, 0)` (Lemma 7.3), and `Z_1 = fit(x_{H'}) + d_1` with `fit(x_{H'})` non-increasing and `d_1` dropping by `h ≥ 1` at `b`; so, if `b^−` is the dancer before `b`, `Z_1(b^−) ≥ Z_1(b) + h`, and `Z_1(b^−) > 0`. So `max(Z_1, 0)` drops strictly at `b`.
   (b) `T = 1`, `sat = 1`, `J' ≡ 0`: the boundary is the middle of the sequence, and `X_1(I') = ŷ'(I') + α2^c ≥ α > 0`; so `Z_1 > 0`, `fit(x_H)` restricted to the first half is `Z_1`, and Lemma 7.2(c) gives the cut at the middle. It is strict: `fit(x_H)` is `Z_1(I') > 0` at `I'` and `min(Z_2({c}), 0) ≤ 0` at `{c}`.
   (c) `T = 0`, `sat = 1`, `J' ≢ 0`: the boundary is `b' ∪ {c}`, with `b'` the boundary of `J'`. Saturation of type `0` means `κ = h` and `τ = h − α2^c`. The second half of the clocks is `x_{H'} + d_2` with `d_2(D_0) = τ − [T = 0]κJ'(D_0) + [T = 1]κJ'(I' ∖ D_0)` (Lemma 7.7), which is non-increasing and changes only at cuts of `x_{H'}`; so the second half is cut at `b' ∪ {c}`, and its integer fit is `X_2 = ŷ' + d_2`. Here `X_2(b') = ŷ'(b') + τ − κ = ŷ'(b') − α2^c ≤ −α < 0`, so the real fit `Z_2` of the second half is negative from `b' ∪ {c}` on, `fit(x_H)_{≥ b'∪{c}} = (Z_2)_{≥ b'∪{c}} = fit((x_H)_{≥ b'∪{c}})`, and Lemma 7.2(c) gives the cut. It is strict: `b' ≠ ∅` (as `J'(∅) = 0`), on the second half `fit(x_H) = min(Z_2, 0)` (Lemma 7.3), and `Z_2 = fit(x_{H'}) + d_2` (Lemma 7.2(b), `b'` being a strict cut of `x_{H'}`) drops by at least `κ = h ≥ 1` at `b' ∪ {c}`, where it is negative. So `min(Z_2, 0)` drops strictly at `b' ∪ {c}`.
   (d) Otherwise `sat = 0`, or `T = 0` and `J' ≡ 0`; then `J_H ≡ 0` (Lemma 7.7), and there is nothing to prove.
   In each case the mirror cut is strict by antisymmetry (§7.1).
4. **The inherited potential.** On the first half put `v'(D_0) := V'(D_0) − [T = 1]κ J'(D_0)`, and on the second half `v'(D_0 ∪ {c}) := τ + V'(D_0) − [T = 0]κ J'(D_0)`. Then `v' = R_H + ω` with `ω(D) := (V' − R_{H'})(D ∩ I')`, and:
   - (G) for `v'`, with **slack `h` on same-half arrows**: `ĉ_H(a, b) ≥ v'(a) − v'(b) + h` if `c ∈ a, b` or `c ∉ a, b`, and `ĉ_H(a, b) ≥ v'(a) − v'(b)` if `c ∈ a ∖ b`. Indeed `v'(a) − v'(b) − R_H(a) + R_H(b) = ω(a) − ω(b) = (V' − R_{H'})(a ∩ I') − (V' − R_{H'})(b ∩ I')`, which is `≤ γ_{I'}((a ∖ b) ∩ I')` by (G) for `H'` (and `0` when `a ∩ I' = b ∩ I'`), and Lemma 7.7 compares `γ_I` with `γ_{I'}`.
   - (E) for `v'` with `X_1`: `v'(D_0) − v'(I ∖ D_0) = (V'(D_0) − V'(I' ∖ D_0)) + d_1(D_0) = ŷ'(D_0) + d_1(D_0) = X_1(D_0)`, by (E) for `H'`; and on the second half with `X_2`.
   - (M) for `v'` inside each half (`V'` is non-increasing and `J'` is an up-set).
5. **The junction.** `v'({c}) − v'(I') = −X_1(I')`, and, by (Λ) for `H'`,
   `−X_1(I') = −ŷ'(I') + τ + [T = 1]κJ'(I') − [T = 0]κJ'(∅) ≤ α(2^c − 1) + h − α2^c = h − α`.
6. **No central flat.** If `X_1(I') > 0`, then `ŷ_H = (X_1, X_2)`, and `V := v'` satisfies (E), (M) (at the junction by step 5) and (G).
7. **The central flat.** If `X_1(I') ≤ 0`, let `F_1 := {X_1 ≤ 0}`, a non-empty final segment of the first half containing `I'`, and `F_2` its mirror, an initial segment of the second half containing `{c}`. Put `F := F_1 ∪ F_2`; `ŷ_H = 0` exactly on `F`. Let `f` be the first dancer of `F_1`, `p` the dancer just before `f` (if any) and `p^* = I ∖ p` the dancer just after `F` (if any). Put
   `c_3 := v'(f) = max_{F_1} v'`,  `c_4 := v'(I ∖ f) = min_{F_2} v'`.
   Then `c_3 − c_4 = X_1(f) ≤ 0` by (E) for `v'`, `c_3 ≤ v'(p)`, `v'(p^*) ≤ c_4`, and `v'(p^*) < v'(p)` (because `v'(p) − v'(p^*) = X_1(p) > 0`). So **the interval `[max(c_3, v'(p^*)), min(c_4, v'(p))]` is non-empty**. Choose an integer `c_F` in it, and put `V := c_F` on `F` and `V := v'` elsewhere.
8. **Checks.** (E): on `F` both sides are `c_F` and `ŷ_H = 0`; off `F` nothing changed. (M): `V` is constant on the segment `F`, and `v'(p) ≥ c_F ≥ v'(p^*)`. (G) for an arrow `a → b` (`b ⊊ a`, so `b` comes before `a` in o-order) with at least one end in `F`. Since `F_1` is a final segment of the first half and `F_2` an initial segment of the second, the cases are:
   - `a ∈ F_2`, `b` before `F`: `c_F ≤ c_4 ≤ v'(a)`, and `v'(a) − v'(b) ≤ ĉ_H(a, b)`.
   - `a ∈ F_1`, `b` before `F` (same half): `c_F ≤ c_4 ≤ v'({c}) ≤ v'(I') + h − α ≤ v'(a) + h − α`, and `ĉ_H(a, b) ≥ v'(a) − v'(b) + h`; so `c_F − v'(b) ≤ ĉ_H(a, b) − α`.
   - `b ∈ F_1`, `a` after `F`: `c_F ≥ c_3 ≥ v'(b)`, and `v'(a) − v'(b) ≤ ĉ_H(a, b)`.
   - `b ∈ F_2`, `a` after `F` (same half): `c_F ≥ c_3 ≥ v'(I') ≥ v'({c}) − h + α ≥ v'(b) − h + α`, and `ĉ_H(a, b) ≥ v'(a) − v'(b) + h`; so `v'(a) − c_F ≤ ĉ_H(a, b) − α`.
   - Both ends in `F`, same half: `ĉ_H(a, b) ≥ v'(a) − v'(b) + h ≥ v'(I') − v'({c}) + h ≥ α > 0`. If both lie in `F_1`, then `v'(a) ≥ v'(I')` and `v'(b) ≤ c_3 ≤ c_4 ≤ v'({c})`; if both lie in `F_2`, then `v'(a) ≥ c_4 ≥ c_3 ≥ v'(I')` and `v'(b) ≤ v'({c})`. Both ends in `F`, `a ∈ F_2` and `b ∈ F_1`: `ĉ_H(a, b) ≥ v'(a) − v'(b) ≥ c_4 − c_3 ≥ 0`.
   In every case `V(a) − V(b) ≤ ĉ_H(a, b)`. ∎

The construction has a plain reading: at each new digit **exactly one new flat appears, mirror-symmetric, and it pays one price, chosen between the dearest dancer of its lower half and the cheapest of its upper half; every other dancer keeps the price it had one digit below.**

### 7.5 Every cell

**Lemma 7.9 (integrality).** In every house the real fit of `x_H` takes integer values. So does the real fit of the clocks of every penalty cell `Cell(H; P_r, P_c)`, and that of `x_H` with its first dancer deleted, in the house `ℓ = 2^k − 1`. Consequently, in each of these the integer fit is the real fit, and it is non-increasing.

*Proof.* Induction on `|I|`. For `I = ∅` the sequence is `(0)`. Let `I ≠ ∅`, with `H'` and `d_1` as in Lemma 7.7. The shift `d_1` is integer, non-increasing, and changes only at cuts of `x_{H'}` (step 1 of the proof of Theorem 7.8); so, by Lemma 7.2(b), the real fit `Z_1` of the first half is `fit(x_{H'}) + d_1`, integral by induction, and by Lemma 7.3 `fit(x_H) = [max(Z_1, 0), min(Z_2, 0)]` is integral. The penalty shift of a cell is integer, non-increasing, and changes only at cuts of `x_H` (Theorem 7.8, (Cut)), so Lemma 7.2(b) again gives an integral fit. In the house `ℓ = 2^k − 1` with `I ≠ ∅`, `x_H` is cut at its second dancer `{t_1}` (Theorem 7.8, (Cut)), so the fit of the sequence without its first dancer is the restriction of `fit(x_H)`. Finally, on a level set of integral value `z` with `p` positions the sum is `S = pz`, so `S mod p = 0` and the integer fit is `z` there. ∎

Strictness is not used in this proof: a cut is enough. As written, strictness is also used in Theorem 7.8 (steps 1 and 3) and in Theorem 7.10, to identify integer fits; with Lemma 7.9 a cut suffices there (in Theorem 7.8 by a joint induction with Lemma 7.9, which uses the (Cut) of Theorem 7.8). It is indispensable only in Proposition 9.6 (H), twice: in the induction for the base cell, and for the penalty shift. Lemma 7.9 also shows that the integer part of Lemma 7.2(b) was never needed beyond integral fits; we keep the strict (Cut) of Theorem 7.8 because Proposition 9.6 needs it.

**Theorem 7.10.** For every family `λ`, every `α ≥ 1` and every shift `i ≥ 1`, `T(r) ≥ Y(r)` for every `r`, and the Smith exponents of `M^{(α)}(λ, i)` are `αK + κ(m, K) + ŷ_D` (`D ⊆ I`), where `ŷ` is the integer fit of the clocks `x_D` of §5. For `i = 0` the Smith exponents are `∞` (once) and `αK + ŷ^♯_D` (`D ≠ ∅`), where `ŷ^♯` is the integer fit of the sequence `x^♯_D` (`D ≠ ∅`) of Proposition 5.4.

*Proof.* *The case `i ≥ 1`.* By Lemma 7.5 the cell is `Cell(H; P_r, P_c)` with `H = (I, k, m mod K, α)`. Let `V` be given by Theorem 7.8 and put `v := V − P_r J_H`, `w := V − P_c J_H`. (U1) holds because `J_H` is an up-set. (U3): `v(a) − w(b) − ĉ(a, b) = V(a) − V(b) − ĉ_H(a, b) ≤ 0` by (G), and it is `0` on loops. (U2): `v(D) − w(I ∖ D) = ŷ_H(D) − P_r J_H(D) + P_c J_H(I ∖ D)`, which is the integer fit of the clocks of the cell by Lemma 7.2(b): the penalty shift `−P_r J_H(D) + P_c J_H(I ∖ D)` is integer, non-increasing, and changes only at the first dancer with `J_H = 1` and at its mirror, which are strict cuts of `x_H` (Theorem 7.8, (Cut)). Theorem 7.4 gives `T(r) ≥ Y(r)`; Lemma 7.9 gives monotonicity, and Theorem 6.5 concludes.
*The case `i = 0`.* The row `∅` of `M(λ, 0)` is zero, so the Smith exponents are `∞` and those of the submatrix `M^♯` of the rows `D ≠ ∅`. By Proposition 5.4 its normalized costs are those of the house `H^♯ = (I, k, K − 1, α)`, for which `J_{H^♯}(D) = [D ≠ ∅]`, and `x^♯_D = x_{H^♯}(D)` for `D ≠ ∅`. If `I ≠ ∅`, the cut of `x_{H^♯}` at the dancer `{t_1}` is strict (Theorem 7.8, (Cut)), so `∅` is a level set by itself, and the fit and the integer fit of `x^♯` (the sequence without `∅`) are those of `x_{H^♯}` restricted to `D ≠ ∅`; if `I = ∅`, `M(λ, 0) = 0`. For `r ≤ N − 1` the rows `L_r` avoid `∅` and the columns `F_r` avoid `I`. So Lemma 6.1, Theorem O, Corollary 6.3 and Lemma 6.4 hold for `M^♯` with the same proofs: they involve only the rows `L_r` and the columns `F_r`, and every entry of `M^♯` in the support is non-zero, because no window of a row `D ≠ ∅` contains `d = 0`; and Theorem 7.4 holds with `v = w = V` restricted to the dancers that occur. ∎

## 8. Proof of the Main Theorem

Let `n ≥ 1`. By Theorem 3.8,
  `ℤ_2 ⊕ Syl_2 K(Q_n) ≅ ⊕_λ X^{(1)}(λ, (n − λ)/2)^{m_λ(n)}`,
the sum over `λ ≡ n (mod 2)` with `1 ≤ λ ≤ n` (Lemma 3.7: `m_0(n) = 0`). Fix a family `λ` and `i = (n − λ)/2`. By Theorem D, `X^{(1)}(λ, i)` is the small clocks plus `coker(2^k M)`, `M = M^{(1)}(λ, i)`.
- If `i ≥ 1`, by Theorem 7.10 (with `α = 1`) the Smith exponents of `M` are `K + κ(m, K) + ŷ_D`, where `ŷ` is the integer fit of the clocks `x_D`. Those of `coker(2^k M)` are `k + K + κ(m, K) + ŷ_D`. By Proposition 5.3 the raw clocks are `u_i(D) = k + K + κ(m, K) + x_D`, and adding an integer constant commutes with the integer fit. So these exponents are the pooled clocks `ŷ_i(D)` of §1.2.
- If `i = 0` (so `λ = n` and `m_n(n) = 1`), the Smith exponents of `M` are `∞` and `K + ŷ^♯_D` (`D ≠ ∅`), and by Proposition 5.4 `u_0(D) = k + K + x^♯_D`. So `coker(2^k M)` is `ℤ_2` (the big clock `ŷ_0(∅) = ∞`) plus the pooled clocks of the sequence `u_0(D)`, `D ≠ ∅`. This is the convention of §1.2: the entry `∞` stands first and is not pooled.
- If `I = ∅`, `M` is `1 × 1`. For `i ≥ 1` its exponent is `K + κ(m, K)` (Proposition 5.2 with `x_∅ = 0`), and `u_i(∅) = φ(K) + κ(i − 1, K) = k + K + κ(m, K)`. For `i = 0`, `M = 0`.

The fits are integral, so the integer fits are the fits themselves, and they are non-increasing (Lemma 7.9). This proves the Main Theorem. ∎

## 9. Consequences

### 9.1 Bai's counts

**Lemma 9.1.** Every raw clock `u_i(D)` with `(i, D) ≠ (0, ∅)` is at least `2`, and so is every pooled big clock.

*Proof.* `φ(ξ) ≥ ξ ≥ 1`, and `κ ≥ 0`. If `ξ = K + o_{I∖D} − o_D = 1`, then, since `o_D ≤ o_I < K`, we need `o_{I∖D} = 0` and `o_D = K − 1`, that is `D = I = [0, k)`; then `h(D) = k ≥ 1` (the family has `λ ≥ 1`). So `u_i(D) ≥ 2`. A level set of numbers that are all `≥ 2` has mean `≥ 2`, and its integer fit takes values `≥ ⌊mean⌋ ≥ 2`. ∎

*Proof of Corollary 1.5.* A copy of a family with `k ≥ 1` contributes
  `Σ_{a=1}^{k−1} 2^{|I|+k−1−a} + 2^{|I|} = 2^{|I|+k−1} = dim T(λ)/2`
cyclic factors, all non-trivial (Lemma 9.1), one of which is `ℤ_2` exactly for `λ = n`. By Lemma 3.7 only families with `k ≥ 1` occur, and `Σ_λ m_λ(n) dim T(λ) = 2^n` (Theorem 3.6). So `Syl_2 K(Q_n)` has `2^{n−1} − 1` cyclic factors. A factor `ℤ/2` can only be a small clock with `a = 1`, and a family with `k ≥ 2` has `2^{|I|+k−2} = dim T(λ)/4` of them. The families with `k ≤ 1` and `λ ≥ 1` are `λ = 1` (`dim 2`) and `λ = 2` (`dim 4`). So the number of factors `ℤ/2` is `(2^n − 2m_1(n) − 4m_2(n))/4`, which by Lemma 3.7 is `2^{n−2} − 2^{(n−3)/2}` for odd `n` and `2^{n−2} − 2^{(n−2)/2}` for even `n ≥ 2`; that is `a_n`. ∎

### 9.2 The podium

In this subsection the family is `λ`, with digits `t_1 < ⋯ < t_s` of `I` (`t_{s+1} := k`), and `P_l := {t_1, …, t_l}`. Put
  `Y_l := λ + 1 − o_{P_l} = K + o(I ∖ P_l)`,  so `v_2(Y_l) = t_{l+1}`,
and `ψ(E) = Σ_{t∈E}(h_t − 2^t)` as in §5, `ψ_t := ψ({t}) = h_t − 2^t`. Recall `g(N) = max_{1≤y<N} φ(y)`.

**Lemma 9.2.** (a) `φ(λ + 1) + ψ(P_l) = φ(Y_l)` for `0 ≤ l ≤ s`. (b) For `N ≥ 1`, `max_{1≤y≤N} φ(y)` is attained at a **clearing** of `N`: a number obtained from `N` by clearing some of its lowest set bits, not all of them. (c) `Y_0, …, Y_s` are the clearings of `λ + 1`; hence `max_l φ(Y_l) = g(λ + 2)`, and `max_{l≥1} φ(Y_l) = max_{1≤y≤Y_1} φ(y)`.

*Proof.* (a) `ψ(P_l) = Σ_{j≤l}(t_{j+1} − t_j) − o_{P_l} = t_{l+1} − t_1 − o_{P_l}`, and `φ(λ + 1) = λ + 1 + t_1`. (b) Given `y ≤ N` with `v_2(y) = q`, let `N_q` be `N` with its bits below `q` cleared. Then `y ≤ N_q`, because `y` is a multiple of `2^q` not above `N`; and `v_2(N_q) ≥ q`, so `φ(N_q) ≥ φ(y)`; and `N_q` is a clearing. (c) is (b) for `N = λ + 1` and `N = Y_1`. ∎

For `N = n − 1`, part (b) is the observation of [GMMY24, Remark 4.4].

**Proposition 9.3 (shift `1`).** Let `i = 1` and write `e(D)` for the pooled big clocks. Then
(a) `e(∅) = max_{0≤l≤s} φ(Y_l)`;
(b) `e(D) ≤ max_{1≤l≤s} φ(Y_l)` for `D ≠ ∅`;
(c) if `0 ∈ I`, then `e({0}) = max_{1≤l≤s} φ(Y_l)`.

*Proof.* At `i = 1`, `m = 0` and `ℓ = 0`. In the house `(I, k, 0, 1)` every window is of type `0` with `κ_t = 1`, no carry is ever born (Lemma 7.6), and `J ≡ 0`. So `R_0 = R_K = ψ` and the cell is its base cell. In the proof of Theorem 7.8 at the level `j` (digit `c = t_j`) the datum `τ` of the window (§7.3) is `ψ_{t_j}`, and `d_1 = −ψ_{t_j}`. With the antisymmetry of `ŷ_{j−1}`, step 1 reads
  `ŷ_j(D_0) = max(ŷ_{j−1}(D_0) − ψ_{t_j}, 0)`  and  `ŷ_j(D_0 ∪ {t_j}) = min(ŷ_{j−1}(D_0) + ψ_{t_j}, 0)`.
Moreover `e(D) = k + K + ŷ_s(D)` and `k + K = φ(λ + 1) + ψ(I)` (proof of Proposition 5.3).
(a) The recursion `y_j = max(y_{j−1} − ψ_{t_j}, 0)` with `y_0 = 0` gives
  `ŷ_s(∅) = max_l (−Σ_{j>l} ψ_{t_j})`.
So `e(∅) = max_l [φ(λ + 1) + ψ(P_l)] = max_l φ(Y_l)`, by Lemma 9.2(a).
(b) Let `b` be the largest index with `t_b ∈ D`. Then `ŷ_b(D ∩ P_b) ≤ 0`, and from level `b` on the same recursion gives `ŷ_s(D) ≤ max_{l≥b}(−Σ_{j>l} ψ_{t_j})`.
(c) `t_1 = 0` and `ψ_0 = h_0 − 1 ≥ 0`, so `ŷ_1({0}) = min(ψ_0, 0) = 0`. From level `1` on, the recursion is that of (a) started at `0`. ∎

**Proposition 9.4 (shift `0`).** Let `λ = n` and `i = 0`, and let `e(D)` (`D ≠ ∅`) be the pooled big clocks. Then
(a) `e({t_1}) = max(φ(Y_1) − 2^{t_1}, max_{2≤l≤s} φ(Y_l))`;
(b) `e(D) ≤ max_{2≤l≤s} φ(Y_l)` for every other `D ≠ ∅`.
(A maximum over an empty set is `−∞`.)

*Proof.* By Theorem 7.10 the clocks are those of the house `H^♯ = (I, k, K − 1, 1)`, shifted by `k + K`, with the dancer `∅` deleted after pooling. In `H^♯` every window is of type `1` and saturated (`κ_t = h_t`, `τ_t = −2^t` in the notation of §7.3), and at every level `J' = [D_0 ≠ ∅]`. So, in step 1 of the proof of Theorem 7.8, `d_1(D_0) = 2^{t_j} − h_{t_j}[D_0 ≠ ∅]`. At level `1` (`I' = ∅`), `X_1(∅) = 2^{t_1}` and `ŷ_1({t_1}) = −2^{t_1}`. At every level `j ≥ 2` a dancer `D_0 ≠ ∅` of the first half follows `y_j = max(y_{j−1} + 2^{t_j} − h_{t_j}, 0)`, where `2^{t_j} − h_{t_j} = −ψ_{t_j}`. Since `k + K − Σ_{j>l} ψ_{t_j} = φ(Y_l)` (as in Proposition 9.3), (a) follows. For (b), let `b ≥ 2` be the largest index with `t_b ∈ D`: at level `b` the value is `≤ 0`, and the recursion takes over. ∎

**Lemma 9.5 (Lemma K).** For `a ≥ 0`, `B ≥ 1` and `q ≥ 0`: `φ(2^q B) + κ(a, B) ≤ max_{1≤y≤2^q(a+B)} φ(y)`.

*Proof.* If `κ(a, B) = 0`, take `y = 2^q B`. Otherwise let the highest carry of `a + B` leave the bit `p − 1`. Carries leave only bits `v_2(B), …, p − 1`, so `κ ≤ p − v_2(B)`. A carry leaves bit `p − 1`, so `(a mod 2^p) + (B mod 2^p) ≥ 2^p` and `(a + B) mod 2^p < a mod 2^p ≤ a`. Then
  `y := 2^q((a + B) − ((a + B) mod 2^p))`
satisfies `y ≤ 2^q(a + B)`, `y ≥ 2^q(B + 1)` and `v_2(y) ≥ q + p`, so `φ(y) > 2^q B + q + v_2(B) + κ = φ(2^q B) + κ`. ∎

**Proposition 9.6 (a ceiling for the big clocks).** In the cube `Q_n`, every big clock of every family at a shift `i ≥ 1` is at most `g(n − i + 1) = max_{1≤y≤n−i} φ(y)`.

*Proof.* *(H) The head is dyadic.* The first level set of the real fit of the clocks of the cell is `{D : D ⊆ P_l}` for some `l`. In the base cell this follows by induction along step 1 of the proof of Theorem 7.8, which keeps the level sets of `fit(x_{H'})` (the house `H'` of Lemma 7.7) because `d_1` changes only at strict cuts (Lemma 7.2(b)). The first level set of the first half is the first level set of `fit(x_{H'})` if `Z_1` is positive there; otherwise `Z_1 ≤ 0` on the whole first half, the fit vanishes on the whole level, and the first level set is everything. The penalty shift of a real cell keeps the level sets, because it changes only at strict cuts (Theorem 7.8, (Cut), and Lemma 7.2(b)); this is where strictness is needed, since a jump of the shift at a cut that is not strict, inside the head, would split it. So the largest big clock is the mean `μ` of the raw clocks `u_i(D)`, `D ⊆ P_l`, which is an integer (Lemma 7.9).
*(M) The mean over a dyadic head.* By steps 1–2 of the proof of Proposition 5.3, `u_i(D) = φ(λ + 1) + 2ψ(D) + κ(m, K + o_{I∖D}) − κ(m, o_D)`. Over `D ⊆ P_l` each digit of `P_l` lies in half the sets, so the mean of `2ψ(D)` is `ψ(P_l)`, and `φ(λ + 1) + ψ(P_l) = φ(Y_l)`. Also `K + o_{I∖D} = Y_l + o_{P_l ∖ D}`, and `D ↦ P_l ∖ D` permutes the subsets of `P_l`. So
  `μ = φ(Y_l) + mean_{D⊆P_l} [κ(m, Y_l + o_D) − κ(m, o_D)]`.
Let `q := t_{l+1} = v_2(Y_l)`, write `m = 2^q m_h + m_ℓ` with `m_ℓ < 2^q`, and put `c_D := [m_ℓ + o_D ≥ 2^q]` (note `o_D < 2^q`). The low parts carry in the same way in both sums, and `s_2(Y_l + o_D) = s_2(Y_l/2^q) + s_2(o_D)`, so
  `κ(m, Y_l + o_D) − κ(m, o_D) = κ(m_h + c_D, Y_l/2^q)`.
*(K) The bound.* Apply Lemma 9.5 with `B = Y_l/2^q` and `a = m_h + c_D`. If `c_D = 1`, then `2^q ≤ m_ℓ + o_D ≤ m_ℓ + o_{P_l}`. In both cases `Y_l + 2^q(m_h + c_D) ≤ Y_l + m + o_{P_l} = λ + 1 + m = n − i`. So every term of the mean is `≤ g(n − i + 1)`, and so is `μ`. ∎

**Lemma 9.7 (multiplicities).** `m_n(n) = 1`; `m_{n−2}(n) = n − 1 − [n even]` for `n ≥ 2`; and for odd `n ≥ 5`,
  `m_{n−4}(n) = (n − 1)(n − 2)/2 − 1 − [n ≡ 1 (mod 4)] ≥ 4`.

*Proof.* By Theorem 3.6 the weight multiplicities of `V^{⊗n}`, `C(n, j)` at `n − 2j`, are `Σ_λ m_λ(n) mult_{n−2j} T(λ)`, and `T(λ)` has highest weight `λ` with multiplicity `1`. From the character of §3.3, `mult_{λ−2} T(λ) = [k ≥ 1] + [0 ∈ I]` (one factor `e^{±1}` turned), and `mult_{λ−4} T(λ) = [k ≥ 2] + [1 ∈ I] + [k ≥ 1][0 ∈ I]` (one factor `e^{±2}`, or two factors `e^{±1}`). For `λ = n`: `0 ∈ I ⟺ n` even, and for odd `n`, `1 ∈ I ⟺ n ≡ 1 (mod 4)`. Peeling at the weights `n − 2` and `n − 4` gives the formulas, with `mult_{n−4} T(n − 2) = 1` for odd `n`. For `n = 5` the last value is `4`, and it increases with `n`. ∎

*Proof of Corollary 1.6.* Let `n ≥ 4` and `G = g(n − 1) = max_{1≤y≤n−2} φ(y)`; `G ≥ φ(n − 2) ≥ n − 2`.
1. *Nothing else rises above `G`.* Small clocks are `≤ k − 1 ≤ log_2(n + 1) − 1 < G`. Shifts `i ≥ 2`: every dancer is `≤ g(n − i + 1) ≤ G` (Proposition 9.6). Shift `1` (the family `n − 2`, where `λ + 1 = n − 1`): by Proposition 9.3 and Lemma 9.2, `e(∅) = max_{y≤n−1} φ(y) = max(G, φ(n − 1))`, and every other dancer is `≤ max_{y≤Y_1} φ(y) ≤ G` because `Y_1 = n − 1 − 2^{t_1} ≤ n − 2`. Shift `0` (the family `n`): by Proposition 9.4 every dancer other than `{t_1}` is `≤ G`, since `Y_l ≤ n + 1 − 2^{t_1} − 2^{t_2} ≤ n − 2` for `l ≥ 2`. The dancer `{t_1}` is at `V_0 = max(φ(n + 1 − 2^{t_1}) − 2^{t_1}, A_0)`, where `A_0 := max_{2≤l≤s} φ(Y_l) ≤ G` (`A_0 = −∞` if `s < 2`). So the factors above `G` are at most the `m_{n−2}(n)` copies of `φ(n − 1)`, when `φ(n − 1) > G`, and the single `V_0`, when `V_0 > G`.
2. *The value of `V_0`.* If `n` is even, `t_1 = 0` and `V_0 = max(φ(n) − 1, A_0)`. If `n ≡ 1 (mod 4)`, `t_1 = 1` and `V_0 = max(φ(n − 1) − 2, A_0)`. If `n ≡ 3 (mod 4)` (or `I = ∅`), `V_0 ≤ G`, because `n + 1 − 2^{t_1} ≤ n − 3`. Also, if `n ≡ 3 (mod 4)`, then `v_2(n − 1) = 1` and `φ(n − 1) − 2 = n − 2 ≤ G`; and if `n` is even, `φ(n − 1) = n − 1 ≤ φ(n − 2) ≤ G`.
3. *Enough factors at `G`.* If `n` is even, each of the `n − 2` copies of the family `n − 2` has two dancers at exactly `G`: `∅`, at `max(G, φ(n − 1)) = G`, and `{0}`, at `max_{y≤n−2} φ(y) = G` (Proposition 9.3(c); `0 ∈ I` because `n − 1` is odd). That is `2(n − 2)` factors at `G`: at least `n + 1` for `n ≥ 6`, which is enough even when `c_1 = G`; for `n = 4`, `c_1 = φ(4) − 1 = 5 > G = 3`, and `2(n − 2) = 4 = n` factors are enough. If `n` is odd, the family `n − 2` gives `n − 1` copies of `∅` at `max(G, φ(n − 1)) ≥ G`. The family `n − 4`, at shift `2`, gives `m_{n−4}(n) ≥ 4` copies of a factor at exactly `G`: there `m = 1`, `0 ∉ I` (`λ` odd), and as in Proposition 9.3 no carry is born and `J ≡ 0`, so the same walk gives `e(∅) = max_{y≤n−3} φ(y) = g(n − 2)`, which is `G` because `φ(n − 2) = n − 2 ≤ φ(n − 3)`.
4. *Reading off.* For `n` even, `c_1 = max(G, φ(n) − 1)` and `c_2 = ⋯ = c_{n+1} = G`. For `n` odd with `φ(n − 1) ≤ G`, nothing lies above `G`, so `c_1 = ⋯ = c_{n+1} = G`. For `n` odd with `φ(n − 1) > G`, the `n − 1` copies of `φ(n − 1)` come first. Then comes `V_0 = φ(n − 1) − 2` if this exceeds `G` (which forces `t_1 = 1`), and otherwise `G`; so `c_n = max(G, φ(n − 1) − 2)` and `c_{n+1} = G`.
The particular cases: `g(n) = max(G, φ(n − 1))`, and `v_2 n + n − 1 = φ(n) − 1`. For `n` odd, `φ(n) − 1 = n − 1 ≤ φ(n − 1) ≤ g(n)`, which gives [GMMY24, Theorems 4.1, 4.2] for `n ≥ 4`. In all cases `c_n = max(G, φ(n − 1) − 2)` and `v_2(n − 1) + n − 3 = φ(n − 1) − 2` (for `n` even, `n − 3 < G`). For `n = 3`, `Syl_2 K(Q_3) = {1: 1, 3: 2}` and the three statements hold. ∎

### 9.3 Gao et al.'s Conjecture 5.4

Write `N := 2^e − 1` and `n := 2^e`.

**Lemma 9.8.** For odd `N'`, the families of `N' + 1` are the `λ + 1`, `λ` a family of `N'`, with `m_{λ+1}(N' + 1) = m_λ(N')` and the same shift. If `λ + 1 = 2^k + Σ_{t∈I} 2^t`, the family `λ + 1` has the same `k` and the set `I ∪ {0}`, with `h'_0 = t_1 := min(I ∪ {k})` and the other gaps unchanged; its small clocks are those of `λ` taken twice, and its dancers are `D` and `D ∪ {0}`, `D ⊆ I`, adjacent in o-order.

*Proof.* Every family of an odd `N'` is odd, and `V·[2l + 1] = [2l + 2]`. Since `λ + 1` is even, `λ + 2 = 2^k + o_I + 1` with `o_I + 1 < 2^k`. ∎

**Lemma 9.9.** Let `J := i + o_D ≥ 1`. In the cube `N`, `u(D) = 2^e − 2J + v_2(J) + s_2(J) + h(D)`. In the cube `n`, for a family with dancer `D'` and `J' := i + o_{D'} ≥ 1`, `u(D') = 2^e + 1 − 2J' + s_2(J' − 1) + h'(D')`.

*Proof.* In the cube `N`, `ξ = λ + 1 − 2o_D = N + 1 − 2J = 2^e − 2J`, and `J ≤ 2^{e−1} − 1`, so `φ(ξ) = 2^e − 2J + 1 + v_2(J)`. With `a = J − 1`, `a + ξ = (2^e − 1) − J` and `ξ/2 = (2^{e−1} − 1) − a`, so `s_2(a + ξ) = e − s_2(J)`, `s_2(ξ) = e − 1 − s_2(a)`, and `κ(a, ξ) = s_2(J) − 1`. In the cube `n`, `ξ' = 2^e + 1 − 2J'` is odd. With `a = J' − 1`, `a + ξ' = (2^e − 1) − a` and `ξ' = (2^e − 1) − 2a`, so `κ(a, ξ') = s_2(a)`. ∎

**Theorem 9.10 (the mirror that doubles).** For every family `λ < N` of the cube `N` (shift `i ≥ 1`) and every `D ⊆ I`, the dancers `D` and `D ∪ {0}` of the family `λ + 1` of the cube `n` have the raw clock `u_N(D)`.

*Proof.* For `D' = D`: `J' = J`, `h'(D) = h(D)`, and `s_2(J − 1) = s_2(J) − 1 + v_2(J)`, so Lemma 9.9 gives `u_n(D) = u_N(D)`. For `D' = D ∪ {0}`: `J' = J + 1` and `h'(D ∪ {0}) = h(D) + t_1`, so `u_n(D ∪ {0}) = u_N(D) + t_1 − 1 − v_2(J)`. Finally, `2i = 2^e − (λ + 1) = 2^e − 2^k − o_I` with `k < e`, so `v_2(i) = t_1 − 1`. Every digit of `D` is `≥ t_1`, so `v_2(J) = v_2(i + o_D) = t_1 − 1`. ∎

*Proof of Corollary 1.7.* By Lemma 9.8 and Theorem 9.10, the raw sequence of `(λ + 1, i)` in o-order is that of `(λ, i)` with every entry written twice. The real fit of a doubled sequence is the doubled fit (Lemma 7.1). A doubled level set, with `2p` positions and sum `2S`, gets `2(S mod p)` copies of `⌈S/p⌉` and the rest `⌊S/p⌋`, the same multiset as two copies of the original. So for `λ < N` the family `λ + 1` of `n` contributes twice what `λ` contributes to `N`, small clocks included. The family `N` of `N` (`I = ∅`) contributes its small clocks and `ℤ_2`. The family `n = N + 1` of `n` (`I = {0}`) contributes these small clocks twice, `ℤ_2`, and the dancer `{0}` at shift `0`, with `ξ = 2^e − 1`, `κ = 0` and `h_0 = e`: `u = 2^e + e − 1`. Cancelling `ℤ_2`, `Syl_2 K(Q_n) ≅ Syl_2 K(Q_N)^2 ⊕ ℤ/2^{2^e + e − 1}`. ∎

## 10. The fold law

### 10.1 The fold on the families

Let `a := x_1 x_2 ⋯ x_n ∈ G`. The folded cube is the Cayley graph of `G/⟨a⟩` with the images of the generators, so its Laplacian acts on `ℤ[G/⟨a⟩] = R/(a − 1)R` as multiplication by `σ`, and `ℤ ⊕ K̄(n) ≅ R/(σR + (a − 1)R)` (for `n ≥ 2` the graph is connected).

**Lemma 10.1.** Under the dictionary of Lemma 2.2, `a` acts on `V^{⊗n}` as
  **`a = (−1)^{(n−H)/2} exp(F)`**,  `exp(F) := Σ_{r≥0} F^{(r)}`.
On a summand `T(λ)` of `V^{⊗n}` at shift `i = (n − λ)/2` this is `a = (−1)^{D + i} exp(F)`, `D` the floor operator of `T(λ)`.

*Proof.* On `V`, `x = 1 − s` acts by `g: b_0 ↦ b_0 − b_1`, `b_1 ↦ −b_1` (Lemma 2.1), and `g = (−1)^{D_V} exp(F)` (`exp(F) b_0 = b_0 + b_1`, `exp(F) b_1 = b_1`). Since `Δ(F^{(r)}) = Σ_{a+b=r} F^{(a)} ⊗ F^{(b)}`, `exp(F)` is group-like, and so is `(−1)^{floor}`; so `a = g^{⊗n}` is `(−1)^{floor} exp(F)` on `V^{⊗n}`, where the floor of a pure tensor is its number of letters `b_1`, `(n − H)/2`. On `T(λ)` the weight is `λ − 2D`, so `(n − H)/2 = D + i`. ∎

Since `a` is expressed through `H` and the divided powers of `F`, it is carried by every isomorphism of `Dist_A`-lattices, and Theorem 3.6 gives, with
  `τ_i := σ^{(1)}_i = F + 2(D + i)` and `X̄(λ, i) := T(λ)/(τ_i T(λ) + (a − 1) T(λ))`  (`a = (−1)^{D+i} exp(F)`):

**Corollary 10.2.** For every `n ≥ 2`, with the multiplicities of Theorem 3.6,
  `ℤ_2 ⊕ Syl_2 K̄(n) ≅ ⊕_λ X̄(λ, (n − λ)/2)^{m_λ(n)}`.

**Proposition 10.3.** If `X̄(λ, i) ≅ 2X(λ, i)` for every `λ ≥ 1` and every `i ≥ 0` (where `X := X^{(1)}`), then Theorem DW holds.

*Proof.* By Theorem 3.8 and Corollary 10.2,
  `ℤ_2 ⊕ Syl_2 K̄(n) ≅ ⊕_λ (2X)^{m_λ(n)} = 2(ℤ_2 ⊕ Syl_2 K(Q_n)) ≅ ℤ_2 ⊕ 2Syl_2 K(Q_n)`;
 cancel `ℤ_2` (the torsion submodule of a finitely generated `ℤ_2`-module is determined). Passing to `2·Syl_2 K(Q_n)` removes exactly the factors `ℤ/2` of `Syl_2 K(Q_n)`, whose number is `a_n` (Corollary 1.5). For `n = 1` both groups are trivial. ∎

So the fold law is a statement family by family. We prove it on the half-size lattice `N := T(l)`, where `λ = 2l + 1` or `λ = 2l + 2`.

### 10.2 The two families on the half-size lattice

On `Φ(N)` put `Ch := Σ_{s≥0} F^{(s)}/(2s − 1)!!` and `Sh := Σ_{s≥0} F^{(s)}/(2s + 1)!!`, operators on `N` (`F = F_N`); `Sh` is invertible. With `u^2 = 2F`, `Ch = cosh(u)` and `Sh = sinh(u)/u` as power series, since `F^{(s)}/(2s − 1)!! = (2F)^s/(2s)!`. For `j ≥ 0` put
  **`Ψ_j := 2(2D + j) + (Ch − (−1)^j)·Sh^{−1}`**  and  **`Σ_c := F + 4(D + c)`**,
operators on `N`. As power series, `(Ch − 1)Sh^{−1} = u·tanh(u/2)` and `(Ch + 1)Sh^{−1} = u·coth(u/2)`, so
  `Ψ_{2c} = 4(D + c) + Σ_{m≥1} η_m F^{(m)}`,  `η_m = 2(2^{2m} − 1)B_{2m}/(2m − 1)!!`,
  `Ψ_{2c−1} = 4(D + c) + Σ_{m≥1} η'_m F^{(m)}`,  `η'_m = 2B_{2m}/(2m − 1)!!`,
with Bernoulli numbers `B_{2m}` (`u^{2m} = 2^m m! F^{(m)}` and `(2m)! = 2^m m!(2m − 1)!!`). By the von Staudt–Clausen theorem [vSt40], [Cla40], `v_2(B_{2m}) = −1`, so every `η_m` and `η'_m` is a `2`-adic unit; `η_1 = 1`, `η'_1 = 1/3`. In particular **`Ψ_j` has the payment `4(D + ⌈j/2⌉)`, an odd constant coefficient of `F`, and constant integral coefficients of `F^{(m)}`, `m ≥ 2`.**

**Lemma 10.4 (odd families).** For `λ = 2l + 1` and every `j ≥ 0`, with `N = T(l)` and `c := ⌈j/2⌉`:
  (a) `X̄(λ, j) ≅ coker(Ψ_j on N)`;  (b) `2X(λ, j) ≅ coker(Σ_c on N)`.

*Proof.* (a) On `T(λ) = Φ(N)`, Proposition 3.1(b) gives `exp(F)(b_0 n) = b_0 Ch(n) + b_1 Sh(n)`. The floor of `b_0 F^{(s)} n` in `T(λ)` is `2(f + s)` and that of `b_1 F^{(s)}n` is one more, so `a(b_0 n) = (−1)^j[b_0 Ch(n) − b_1 Sh(n)]`. Since `Sh` is invertible, `{b_0 n, a b_0 n}` (`n` over a basis of `N`) is a basis of `T(λ)`, which is therefore free over `A[a]/(a^2 − 1)`. From `b_1 n = b_0 Ch Sh^{−1} n − (−1)^j a b_0 Sh^{−1} n` and `τ_j(b_0 n) = b_1 n + 2(2f + j) b_0 n`, `τ_j` has the matrix `[[P, Q], [Q, P]]` in this basis, with `P = Ch Sh^{−1} + 2(2D + j)` and `Q = (−1)^{j+1} Sh^{−1}`. On the coinvariants `T(λ)/(a − 1)T(λ) ≅ N`, `τ_j` acts as `P + Q = Ψ_j`.
(b) By Proposition 4.1 with `α = 1`, `X(λ, j) ≅ coker(2G')`, with `G' = F + π'(D)` on `N` and
  `π'(f) = −2(j + 2f)(j + 2f + 1) = −4(c + f) u_f`,
where `u_f` is odd (`u_f = j + 2f + 1` for even `j`, `j + 2f` for odd `j`). So `2X(λ, j) ≅ coker G'`. Right multiplication by the floor unit `(−u(D))^{−1}` and conjugation by the floor units `s(D)` with `s(f + 1) = −u_f^{−1} s(f)` turn `G'` into `Σ_c` and do not change the cokernel. ∎

For operators `X`, `Y` on `N`, put on `N ⊕ N`
  **`glue(X, Y) := [[X, 0], [(Y − X)/2, Y]]`**,
so that `glue(X, Y) = L^{−1} diag(X, Y) L` with `L = [[1, 0], [1/2, 1]]`, and `glue(X, Y)·glue(X', Y') = glue(XX', YY')`.

**Lemma 10.5 (even families).** For `λ = 2l + 2`, `N = T(l)` and every `i ≥ 0`:
  (a) `X̄(λ, i) ≅ coker(glue(Ψ_{i+1}, Ψ_i) on N ⊕ N)`;
  (b) `2X(λ, i) ≅ coker(glue(Ψ_{i+1}(Ψ_{i+1} − 2)/2, Ψ_i(Ψ_i + 2)/2) on N ⊕ N)`.

*Proof.* Let `ν = 2l + 1`, so `T(λ) = V ⊗ T(ν)` (§3.3) at the same shift `i`. By Lemma 10.1 and the coproduct, on `V ⊗ M` (`M = T(ν)`) we have `a = g ⊗ a_M` and `τ_i = (1 − g) ⊗ 1 + 1 ⊗ τ_M`. Here `(1 − g)b_0 = b_1` and `(1 − g)b_1 = 2b_1`, and `V ≅ A[g]/(g^2 − 1)` is the regular module with generator `b_0`.
- Modulo `a − 1`, `g ≡ a_M`, so `X̄(λ, i) ≅ coker(f on M)` with `f := 1 + τ_M − a_M`.
- Modulo `τ_i`, `g ≡ 1 + τ_M`, so `X(λ, i) ≅ M/((1 + τ_M)^2 − 1)M = coker(τ_M(τ_M + 2))`. With `J = D + i` and `JF = F(J + 1)`, `τ_M(τ_M + 2)/2 = F^{(2)} + 2F(J + 1) + 2J(J + 1)` is integral, so `2X(λ, i) ≅ coker(θ on M)` with `θ := τ_M(τ_M + 2)/2 = f·h`, `h := (1 + τ_M + a_M)/2`.

Now `M = Φ(N)`, and by the proof of Lemma 10.4(a) every `w ∈ A[τ_M, a_M]` has the circulant matrix `[[X, Y], [Y, X]]` in the basis `(b_0 N, a·b_0 N)`. Adding column 2 to column 1, subtracting row 1 from row 2, and exchanging the two slots give
  `coker(w) ≅ coker(glue(w_−, w_+))`,
where `w_+ := X + Y` and `w_− := X − Y` are the actions of `w` on the coinvariants and the anti-coinvariants of `a_M`. They are ring maps, with `τ_M ↦ P + Q = Ψ_i`, `a_M ↦ 1`, and `τ_M ↦ P − Q = Ψ_{i+1} − 2`, `a_M ↦ −1`. So `f_+ = Ψ_i`, `f_− = Ψ_{i+1}`, `θ_+ = Ψ_i(Ψ_i + 2)/2` and `θ_− = Ψ_{i+1}(Ψ_{i+1} − 2)/2`. ∎

So the fold law asks: (odd) `coker Ψ_j ≅ coker Σ_{⌈j/2⌉}` on `T(l)`; (even) the two glued systems of Lemma 10.5 have the same cokernel. Note `Ψ_{i+1} − Ψ_i = 2(1 + (−1)^i Sh^{−1})`.

### 10.3 The formal dance

The operators of §10.2 are not payment systems: they carry the divided powers `F^{(m)}`, `m ≥ 2`. We extend the dance of §4 to them.

**Formal operators.** Let `𝔅` be the set of formal sums `x = Σ_{m≥0} x_m(D) F^{(m)}`, where each `x_m` is a function `ℤ_{≥0} → ℚ_2` (the *coefficient at the target floor*), with the product
  `(xy)_m(f) = Σ_{a+b=m} C(m, a)·x_a(f)·y_b(f − a)`.
It is an associative `ℚ_2`-algebra (the rule is that of `F^{(a)}F^{(b)} = C(a+b, a)F^{(a+b)}` and `F^{(a)}p(D) = p(D − a)F^{(a)}` for a function `p` of the floor), and `x` is *integral* if every `x_m` takes values in `A`. An element of `𝔅` acts on every floor-graded lattice with divided powers of `F` — in particular on every `T(l)` — by `x·v = Σ_m x_m(f + m) F^{(m)} v` for `v` of floor `f` (a finite sum), and this is a ring homomorphism. A value `x_m(g)` with `g < m` never acts, and we identify two formal sums that agree at every `g ≥ m`; then the action on all the `T(l)` together is faithful, because on the sublattice generated by the top vector of `T(l)` the operator `F^{(m)}` sends the vector of floor `g` to `C(g + m, m)` times the vector of floor `g + m`, which is non-zero for `g + m ≤ l`. A *system of size `r`* is an `r × r` matrix `G = (G[s, s'])` over `𝔅`, acting on `N^{⊕r}`; `G[s, s']` maps the slot `s'` (the *source*) to the slot `s` (the *coordinate*). The operators `σ^{(α)}_i`, `Ψ_j`, `Σ_c`, their products, and the glued operators of Lemma 10.5 are systems of size `1` or `2`.

**The twist map.** On `Φ(N')`, Proposition 3.1(b) writes the action of `x ∈ 𝔅` in the slots `b_0 ⊗ N'`, `b_1 ⊗ N'` as the block matrix `[[x^{00}, x^{01}], [x^{10}, x^{11}]]` (coordinate slot first, source slot second), with `D`, `F` those of `N'`:
  `x^{00} = Σ_q x_{2q}(2D) F^{(q)}/(2q − 1)!!`,  `x^{11} = Σ_q x_{2q}(2D + 1) F^{(q)}/(2q − 1)!!`,
  `x^{10} = Σ_q x_{2q+1}(2D + 1) F^{(q)}/(2q + 1)!!`,  `x^{01} = Σ_q ((2q + 2)/(2q + 1)!!)·x_{2q+1}(2D) F^{(q+1)}`.
(The floor of `b_e ⊗ n'` is `2f + e`; for instance `F^{(2q+1)}(b_1 n') = ((2q+2)/(2q+1)!!)·b_0 F^{(q+1)}n'` lands at the floor `2(f + q + 1)`.) The denominators are odd. Since this is the action on `Φ(N')` for every `N'`, and the action is faithful, `x ↦ [[x^{00}, x^{01}], [x^{10}, x^{11}]]` is multiplicative; it is applied entrywise to systems.

**The `V`-split.** On `V ⊗ M`, `F^{(m)} = 1 ⊗ F^{(m)} + F ⊗ F^{(m−1)}` and the floor of `b_v ⊗ y` is `v` plus the floor of `y`. So the action of `x` in the slots `b_0 ⊗ M`, `b_1 ⊗ M` is
  `[[x, 0], [x', x^+]]`,  `x^+_m(g) := x_m(g + 1)`,  `x'_{m−1}(g) := x_m(g + 1)` (`m ≥ 1`),
operators on `M`: a system of size `r` on `V ⊗ M` becomes a system of size `2r` on `M`.

**The moves.** Let `G` be a system of size `r` on `N`.
- If `N = Φ(N')`, apply the twist map. Order the coordinates as (the `b_1`-slots, the `b_0`-slots) and the sources as (the `b_0`-slots, the `b_1`-slots); then `G = [[P, C], [B, Dd]]` with **pivot** `P := G^{10}`, `C := G^{11}`, `B := G^{00}`, `Dd := G^{01}`, blocks of size `r` over `𝔅'`.
- If `N = V ⊗ Φ(N')`, first `V`-split (size `2r` on `Φ(N')`), then proceed as in the first case.
The move is **clean** if `P` is invertible on `N'^{⊕r'}` and `S := Dd − B P^{−1} C ≡ 0 (mod 2)`; then the **next system** is `G' := S/2`, of size `r' = r` or `2r` on `N'`. The **dance** of a system `G` on `T(l)` along the word `w` of `l` (§4.3: the digits `t = 0, …, k − 1` of `l + 1 = 2^k + Σ_{t∈I} 2^t`, a twist move if `t ∉ I`, a split move if `t ∈ I`) is the sequence `G_0 = G, G_1, …, G_k`; it is **clean** if every move is clean, and then its **final matrix** is `M_w(G) := G_k`, a matrix over `A` of size `r·2^{|I|}` (on `T(0) = A`, `F` acts as `0`). The final slots are indexed by `(s, D)`, `s` a slot of `G` and `D ⊆ I` a dancer, as in §4.3.

**Lemma 10.6.** (a) For an even payment system the twist move is the elimination of Proposition 4.1, and the split move (`V`-split followed by the twist move) has the same next system as Proposition 4.2. (b) Hence the dance of `σ^{(α)}_c` on `T(l)` is clean and **`M_w(σ^{(α)}_c) = M^{(α)}(l, c)`**, the matrix of Theorem 4.4; and for a unit `u ∈ A`, `M_w(uG) = u·M_w(G)`.

*Proof.* (a) For an even payment system `G = F + π(D) + K(D)` (couplings of degree `0`), `P = G^{10}` is the identity, `B = (π + K)(2D)`, `C = (π + K)(2D + 1)` and `Dd = 2F`, so `S/2 = F − ½(π + K)(2D)·(π + K)(2D + 1)`, which is `G'` of Proposition 4.1 (expand the product of the two triangular matrices). So the twist move is clean: `P` is invertible, and `S = 2G'` with `G'` even (Proposition 4.1), so that the next move applies to `G'`. For the split move, Proposition 4.2 eliminates the coordinates `B_n`, `Dd_n` against the sources `A_n`, `C_n`, in the basis `(A_n, B_n, C_n, Dd_n)`; the `V`-split followed by the twist move eliminates the coordinates `b_0 ⊗ b_1 n`, `Dd_n` against the same sources `A_n`, `C_n`, in the basis `(A_n, b_0 ⊗ b_1 n, C_n, Dd_n)`. The two bases differ by `B_n = b_0 ⊗ b_1 n − C_n`. In the matrix of `G`, this replaces the remaining column of the source `b_0 ⊗ b_1 n` by itself minus the pivot column of `C_n`, and the remaining row of the coordinate `C` by itself plus the pivot row of the coordinate `b_0 ⊗ b_1`; the pivot block does not change. Neither operation changes the Schur complement: for a pivot row `p`, `M_{p,c} − M_{p,P} M_{P,P}^{−1} M_{P,c} = 0`, and symmetrically for a pivot column. So the two next systems coincide, slot `(s, A)` with the dancer `v = 0` and slot `(s, C)` with `v = 1`; and the split move is clean, because its pivot block is the one eliminated in Proposition 4.2 (triangular, with the coefficient `1` on each eliminated vector) and `S = 2G''` with `G''` even (Proposition 4.2).
(b) By (a) and Proposition 4.3. For the last claim, `uDd − uB(uP)^{−1}uC = uS`. ∎

**Proposition 10.7.** Let `G` be a system of size `r` on `T(l)` whose dance is clean. Then
  **`coker(G on T(l)^{⊕r}) ≅ ⊕_{a=1}^{k−1} (ℤ/2^a)^{r·2^{|I|+k−1−a}} ⊕ coker(2^k M_w(G))`.**
In particular, two systems of the same size on `T(l)` with clean dances and final matrices of equal Smith form have isomorphic cokernels.

*Proof.* If `P` is invertible, unimodular row and column operations turn `[[P, C], [B, Dd]]` into `diag(P, S)` and then into `diag(1, S)`; so `coker(2^h G_h) ≅ (ℤ/2^h)^{rank P} ⊕ coker(2^h S) = (ℤ/2^h)^{rank P} ⊕ coker(2^{h+1} G_{h+1})`. Count the ranks as in Proposition 4.3. ∎

### 10.4 Rigidity: the inverse block

In this section `G = Ξ` is a system of size `1` on `T(l)`, `l + 1 = 2^k + Σ_{t∈I} 2^t`, `K = 2^k`. A dancer of level `h` is a subset `D` of `I ∩ [0, h)`.

**Lemma 10.8 (inverse block).** Suppose `Ξ` is invertible on `T(l) ⊗ ℚ` and every pivot met by its dance is invertible over `ℚ_2`. Then for every level `h`,
  **`G_h^{−1} = 2^h·out_h ∘ Ξ^{−1} ∘ in_h`,**
where `in_h` sends the coordinate `(D, g)` of level `h` (dancer `D`, level-`h` floor `g`) to a vector of `T(l)` of floor `2^h g + o_D`, `out_h` reads the source `(D, g)` of level `h` off the vectors of `T(l)` of floor `2^h g + o_D + 2^h − 1`, and both are fixed by the word `w` alone.

*Proof.* In the order of §10.3, `G_h = [[P, C], [B, Dd]]` with `P` invertible; since `G_h` is invertible, so is `S`, and the block of `G_h^{−1}` on (the remaining sources) × (the remaining coordinates) is `S^{−1}` (the standard identity for the inverse of a block matrix). So `G_{h+1}^{−1} = 2S^{−1}` is `2` times a block of `G_h^{−1}`; compose over the levels. The remaining coordinates of a twist move are the `b_0`-slots, of level-`h` floor `2g`, and the remaining sources the `b_1`-slots, of level-`h` floor `2g + 1`; after a `V`-split, the dancer `v` adds `v` to the level-`h` floor. By induction, a coordinate of level `h` sits at the floor `2^h g + o_D` of `T(l)` and a source at `2^h g + o_D + (2^h − 1)`: a twist move, or a split move with `v = 0`, adds `0` to the coordinate offset and `2^h` to the source offset; a split move with `v = 1` adds `2^h` and `2^{h+1}`. ∎

**Corollary 10.9.** Suppose `Ξ^{−1} = Σ_L y_L(D) F^{(L)}` in `𝔅`. Then for dancers `X, Y ⊆ I`,
  **`(M_w(Ξ)^{−1})_{YX} = 2^k·γ_{YX}·y_{L}(o_Y + K − 1)`,  `L := o_Y − o_X + K − 1`,**
where `γ_{YX} ∈ ℚ_2` depends only on the word `w`, and `γ_{YX} = 0` if `L < 0`. The floors visited form the **window** `[o_X, o_Y + K − 1]`, which is the window of Theorem 4.4.

*Proof.* `in(e_X)` has floor `o_X` and `out` reads the source `Y` at floor `o_Y + K − 1`; of
  `Ξ^{−1} in(e_X) = Σ_L y_L(o_X + L) F^{(L)} in(e_X)`
only the term `L = o_Y − o_X + K − 1` has that floor. Put `γ_{YX} := out_Y(F^{(L)} in(e_X))`. ∎

From now on let `α ≥ 2`, `c ≥ 1`, `η ∈ A` a unit, and
  **`Σ := 2^α(D + c) + ηF`,  `Ξ := Σ + Σ_{m≥2} ζ_m(D) F^{(m)}`,**
with integral functions `ζ_m`. Put `π(d) := 2^α(d + c) ≠ 0` and `ζ_1 := η`.

**Lemma 10.10 (path sum).** For every `L ≥ 0` and every floor `f`,
  `y^Ξ_L(f) = y^Σ_L(f)·(1 + e_L(f))`  with  **`v_2(e_L(f)) ≥ α − 1`**,  and  `y^Σ_L(f) = (−1)^L L! η^L / ∏_{d=f−L}^{f} π(d)`.

*Proof.* Write `Ξ = π(D) + N`. Then `Ξ^{−1} = Σ_{s≥0} (−1)^s (π(D)^{−1}N)^s π(D)^{−1}`, and the coefficient of `F^{(L)}` at the target floor `f` is the sum, over the compositions `L = m_1 + ⋯ + m_s` (landing floors `f − L = f_0 < f_1 < ⋯ < f_s = f`), of
  `(−1)^s (L!/∏ m_i!)·∏_i ζ_{m_i}(f_i) / ∏_{j=0}^{s} π(f_j)`.
For `Σ` only the composition `1 + ⋯ + 1` occurs. Any other composition, divided by that term, is `± ∏_i ζ_{m_i}(f_i)·η^{−L}/∏_i m_i!` times the payments of the `Σ_i (m_i − 1)` floors of `[f − L, f]` that it skips; its valuation is at least `Σ_i [α(m_i − 1) − v_2(m_i!)] ≥ (α − 1)Σ_i (m_i − 1) ≥ α − 1`, since `v_2(m!) ≤ m − 1`. ∎

The final matrix of `Σ` is known. By Lemma 10.6(b), `M_w(Σ) = η·M_w(F + η^{−1}π(D))`, and the proof of Theorem 4.4 uses only the products of the payment over windows. So, with `𝒜` the matrix of multiplication by `q_k` in the basis `y^D` (`𝒜_{DD'} = a_k(D ∖ D')` if `D' ⊆ D`, else `0`):
  **`M_w(Σ) = 𝔡_1·𝒜·𝔡_2`,**  `(𝔡_1)_D = −2^{1−K} η^{1−K}·(2η)^{o_D}/∏_{d<o_D} π(d)`,  `(𝔡_2)_{D'} = (2η)^{−o_{D'}}·∏_{d ≤ o_{D'}+K−1} π(d)`,
diagonal and invertible, and `v_2(𝒜_{DD'}) = δ(D ∖ D')` exactly (Lemma 4.5).

For matrices `B`, `E` of the same size, `B ∘ (1 + E)` is the matrix with entries `B_{ij}(1 + E_{ij})`.

**Lemma 10.11 (stability).** If `v_2(E_{ij}) ≥ 1` for all `i, j`, then `(M_w(Σ)^{−1} ∘ (1 + E))^{−1} = M_w(Σ) ∘ (1 + E')` with `v_2(E'_{ij}) ≥ 1` for all `i, j`.

*Proof.* Diagonal scalings commute with `∘`, so it suffices to treat `𝒜`. Its inverse `𝒜^{−1}` is multiplication by `q_k^{−1} = Σ_j (1 − q_k)^j` (`q_k` has constant term `1` for `k ≥ 1`; for `k = 0` everything is `1 × 1`); its `(D, D')` entry is a sum over the ordered partitions of `D ∖ D'` into non-empty blocks `B_1, …, B_j` of `± a_k(B_1)⋯a_k(B_j)`, so by the strict subadditivity of `δ` (§4.5) `v_2((𝒜^{−1})_{DD'}) ≥ δ(D ∖ D')`, and it vanishes unless `D' ⊆ D`. Put `B := 𝒜^{−1}`. Then `(B ∘ (1 + E))^{−1} = (1 + 𝒜(B ∘ E))^{−1}𝒜 = Σ_{j≥0} (−1)^j [𝒜(B ∘ E)]^j 𝒜`, which converges because `𝒜(B ∘ E) ≡ 0 (mod 2)`. The `(D, D')` entry of the `j`-th term is a sum over chains `D ⊇ E_1 ⊇ F_1 ⊇ ⋯ ⊇ E_j ⊇ F_j ⊇ D'` of products whose valuation is at least `δ(D ∖ E_1) + δ(E_1 ∖ F_1) + 1 + ⋯ + δ(F_j ∖ D')`, which is `≥ δ(D ∖ D') + j` by subadditivity. Since `v_2(𝒜_{DD'})` is exactly `δ(D ∖ D')`, the terms `j ≥ 1` change `𝒜_{DD'}` by a factor `1 + E'_{DD'}` with `v_2(E'_{DD'}) ≥ 1`, and they vanish where `𝒜` does. ∎

**Theorem 10.12 (rigidity).** If the dance of `Ξ` along `w` is clean, then **`M_w(Ξ) = M_w(Σ) ∘ (1 + E')` with `v_2(E') ≥ 1` entrywise**. Consequently `M_w(Ξ)` and `M_w(Σ)` have the same support and the same entry valuations, the same Smith form, and **`coker(Ξ on T(l)) ≅ coker(Σ on T(l)) ≅ X^{(α)}(l, c)`.**

*Proof.* The dance of `Σ` is clean (Lemma 10.6). By Corollary 10.9 for `Ξ` and for `Σ`, with the same `γ`, and Lemma 10.10, `M_w(Ξ)^{−1} = M_w(Σ)^{−1} ∘ (1 + E)` with `v_2(E) ≥ α − 1 ≥ 1`; Lemma 10.11 inverts this. The Smith form of `M^{(α)}(l, c)` is computed in Theorems 6.5 and 7.10 from the valuations of its entries and from its support alone: the tropical bound (Lemma 6.1) and the unique golden matching (Theorem 6.2) see nothing else. Since `M_w(Σ) = η·M_w(F + η^{−1}π(D))` has the valuations and the support of `M^{(α)}(l, c)` (Theorem D, with the payment `η^{−1}π`), all three matrices have the same Smith form. Proposition 10.7 gives the cokernels; and `coker Σ ≅ coker(F + π(D))` because `η^{−D}(ηF + π(D))η^{D} = F + π(D)`. ∎

**The case `c = 0`.** Then `π(0) = 0` and `Ξ` is not invertible. We treat it by continuity in §10.6.

### 10.5 Cleanliness: the ring 𝒦

Theorem 10.12 needs the dance of `Ξ` to be clean. This is not automatic: the payments are functions of the floor, and the moves mix floors.

**Positions.** At level `h` the dancers are the subsets `D` of `P_h := I ∩ [0, h)`. The **position** of the dancer `D` at the level-`h` floor `f` is
  **`y := 2^h f + o_D + c`**,
where `c` is a fixed element of `ℤ_2` (the shift). A system `G` of level `h` is **covariant** if `G[D, D'] = 0` unless `D' ⊆ D`, and there are functions `Γ_{Δ,m}` such that
  `G[D, D']_m(f) = Γ_{D∖D', m}(2^h f + o_D + c)`
(the coefficient of `F^{(m)}` at the target floor `f` depends only on `Δ = D ∖ D'`, `m` and the position of the target).

**The ring 𝒦.** Let **`𝒦`** be the set of functions `ϑ: ℤ_2 → ℤ_2` of the form
  **`ϑ(y) = a + 2χ(2y)`,  `a ∈ ℤ_2`, `χ ∈ X·ℤ_2[[X]]`**
(the series converges at `X = 2y`).

**Lemma 10.13.** (a) The representation `(a, χ)` of `ϑ ∈ 𝒦` is unique. The set `𝒦` is a ring, it is stable under every shift `y ↦ y − e` (`e ∈ ℤ_2`), and `1/ϑ ∈ 𝒦` when `a` is odd.
(b) Let `𝒮 := 𝔽_2 ⊕ ε·X 𝔽_2[[X]]` with `ε^2 = 0`, a commutative ring of characteristic `2`, and `Θ(ϑ) := ā + ε χ̄` (reductions modulo `2`). Then **`Θ: 𝒦 → 𝒮` is a ring homomorphism, `Θ(ϑ(· − e)) = Θ(ϑ)` for every `e ∈ ℤ_2`, and `ker Θ = 2𝒦`.**
(c) `ϑ(y) ≡ a (mod 4)` for every `y`.

*Proof.* (a) If `a + 2χ(2y) = a' + 2χ'(2y)` for all `y ∈ ℤ_2`, the power series `(a − a') + 2(χ − χ')(2Y)` in `Y` has coefficients tending to `0` and infinitely many zeros, so it vanishes by Strassmann's theorem [Str28].
*Products.* `(a + 2χ)(b + 2ω) = ab + 2(aω + bχ + 2χω)`.
*Shifts.* `χ(X − 2e) = χ(−2e) + χ̃(X)` with `χ̃ ∈ X ℤ_2[[X]]`, and `χ(−2e) ∈ 2ℤ_2`.
*Inverses.* `(a + 2χ)^{−1} = a^{−1} Σ_{j≥0} (−2χ/a)^j`.
(b) The product rule in (a) reduces to `(ā + εχ̄)(b̄ + εω̄)`. Modulo `2`, the coefficient `Σ_{n≥j} c_n C(n, j)(−2e)^{n−j}` of `X^j` in `χ̃` is `≡ c_j`, and `2χ(−2e) ∈ 4ℤ_2`; so `Θ` is shift-invariant. Finally, `Θ(ϑ) = 0` means `a`, `χ` even, `ϑ = 2(a/2 + 2(χ/2)(2y))`.
(c) `2χ(2y) ∈ 4ℤ_2`. ∎

Let `𝒯_h` be the set of covariant systems of level `h` whose functions `Γ_{Δ,m}` all lie in `𝒦`, and let `R_𝒮 := 𝒮[F^{(m)} : m ≥ 1][E_t : t ∈ P_h]/(E_t^2)`, a commutative ring (divided-power multiplication in `F`).

**Lemma 10.14.** (a) `𝒯_h` is a ring.
(b) **`Θ_h(G) := Σ_{Δ,m} Θ(Γ_{Δ,m}) F^{(m)} E^Δ`** (`E^Δ := ∏_{t∈Δ} E_t`) is a ring homomorphism `𝒯_h → R_𝒮`.
(c) In `R_𝒮`, every element `β` satisfies `β^2 = β_0^2`, where `β_0` is its constant term.

*Proof.* (a) For `G, H ∈ 𝒯_h`,
  `(GH)[D, D']_m(f) = Σ_{D ⊇ D_1 ⊇ D'} Σ_{a+b=m} C(m, a)·Γ^G_{D∖D_1, a}(y)·Γ^H_{D_1∖D', b}(y − a·2^h − o_{D∖D_1})`,
because the position of `(D_1, f − a)` is `y − a·2^h − o_{D∖D_1}` (`o` is additive on disjoint sets). The sum over `D_1` is a sum over the decompositions `Δ = (D ∖ D_1) ⊔ (D_1 ∖ D')`, so it depends only on `Δ`, `m` and `y`, and lies in `𝒦` by Lemma 10.13(a). (b) Apply `Θ` to this formula: by shift-invariance the shifts disappear, and the sum over decompositions of `Δ` is the product of the `E^Δ`. (c) `R_𝒮` is commutative of characteristic `2`, so `β^2 = Σ_μ β_μ^2 μ^2` over the monomials `μ = F^{(q)}E^Δ`, and `μ^2 = C(2q, q)F^{(2q)}E^{2Δ} = 0` unless `μ = 1` (`C(2q, q)` is even for `q ≥ 1`, and `E_t^2 = 0`). ∎

**Theorem 10.15 (cleanliness).** Let `G_h ∈ 𝒯_h` satisfy
  (a) the payments are `≡ 0 (mod 4)`: `Γ_{∅,0}(y) ∈ 4ℤ_2` for every `y`;
  (b) the diagonal coefficients of `F` are odd: `Γ_{∅,1}(y)` is a unit for every `y`.
Then the move of level `h` is clean, and `G_{h+1} ∈ 𝒯_{h+1}` again satisfies (a) and (b). Consequently, **for every `α ≥ 2`, every `c ∈ ℤ_2`, every unit `η` and all constants `ζ_m ∈ ℤ_2`, the dance of `2^α(D + c) + ηF + Σ_{m≥2} ζ_m F^{(m)}` on every `T(l)` is clean.**

*Proof.* *The twist move.* The level does not change the dancers. The position of `(D, f')` at level `h + 1` is `y' = 2^{h+1} f' + o_D + c`; the level-`h` floors `2f'` and `2f' + 1` have the positions `y'` and `y' + 2^h`. By the formulas of §10.3 the blocks have the coefficient functions
  `B`: `Γ_{Δ,2q}(y')/(2q − 1)!!`,  `C`: `Γ_{Δ,2q}(y' + 2^h)/(2q − 1)!!`,
  `P`: `Γ_{Δ,2q+1}(y' + 2^h)/(2q + 1)!!`,  `Dd`: `((2q + 2)/(2q + 1)!!)·Γ_{Δ,2q+1}(y')`
(the last is the coefficient of `F^{(q+1)}`). All four lie in `𝒯_{h+1}` (Lemma 10.13(a); the denominators are odd). The diagonal constant term of `P` is `Γ_{∅,1}(y' + 2^h)`, a unit by (b), and the other terms of `P` raise `m` or `Δ`; so `P^{−1}` exists, is integral and lies in `𝒯_{h+1}` (a Neumann series in which each coefficient receives finitely many terms). So `S = Dd − B P^{−1} C ∈ 𝒯_{h+1}`. Apply `Θ_{h+1}`: `Θ(Dd) = 0`, because every coefficient of `Dd` is `(2q + 2)` times an element of `𝒦`; `Θ(B) = Θ(C) =: β`, because the shift by `2^h` is invisible to `Θ`. In the commutative ring `R_𝒮`,
  **`Θ(S) = −β·Θ(P)^{−1}·β = −β^2·Θ(P)^{−1}`,**
and `β^2 = Θ(Γ_{∅,0})^2` by Lemma 10.14(c). By (a) and Lemma 10.13(c) the constant `a` of `Γ_{∅,0}` is even, so `Θ(Γ_{∅,0}) = εχ̄` and `β^2 = ε^2 χ̄^2 = 0`. So every coefficient function of `S` lies in `ker Θ = 2𝒦`: the move is clean and `G_{h+1} = S/2 ∈ 𝒯_{h+1}`. For (a): the new payment is `−Γ_{∅,0}(y')·Γ_{∅,1}(y' + 2^h)^{−1}·Γ_{∅,0}(y' + 2^h)/2` (only constant terms contribute to the constant term, and `Dd` has none), which is `≡ 0 (mod 8)`. For (b): the coefficient of `F^{(1)}` on the diagonal of `S` is `2Γ_{∅,1}(y')` (from `Dd`) minus terms of `BP^{−1}C` that each contain a constant term of `B` or of `C`, that is a payment `≡ 0 (mod 4)`; after division by `2` it is odd.
*The split move.* First the `V`-split: by §10.3 the dancer `D` gives the dancers `D` (`v = 0`) and `D ∪ {h}` (`v = 1`); the position of `(D ∪ {h}, g)` is `2^h(g + 1) + o_D + c = 2^h g + o_{D∪{h}} + c`, so the diagonal blocks keep their functions `Γ_{Δ,m}`, and the new coupling from `D'` to `D ∪ {h}` has `Γ^{new}_{Δ∪{h}, m−1} := Γ_{Δ, m}` at the same position. The split system is covariant with functions in `𝒦` and still satisfies (a), (b). It has couplings with an odd constant term (`Γ^{new}_{{h},0} = Γ_{∅,1}`); they are harmless, because in `R_𝒮` they carry `E_h` and `E_h^2 = 0`, so they do not enter `β^2`. Then the twist move, as above, with the dancers of `P_{h+1}`.
*The operators.* At level `0` the only dancer is `∅`, the position is `y = f + c`, and `Γ_{∅,0}(y) = 2^α y = 2χ(2y)` with `χ(X) = 2^{α−2}X`, which is in `𝒦` because `α ≥ 2`; `Γ_{∅,1} = η`, `Γ_{∅,m} = ζ_m`. ∎

**Remarks.** (1) At `α = 1` the payment `2y` is not in `𝒦` (`χ` would be `X/2`), and the cleanliness of the dance of `σ^{(1)}_i` (Lemma 10.6) comes from the fact that it is an even payment system. (2) The class `𝒦` is sufficient, not necessary: every even payment system dances clean, whatever its payments (proof of Lemma 10.6(a), with Propositions 4.1 and 4.2). With higher divided powers some restriction is needed. We measured the dances on `T(l)`, `l = 2, …, 63`, of `p(D) + u(D)F + Σ_{m≥2} ζ_m F^{(m)}` with constant random integers `ζ_m ∈ [−5, 5]`, four for each `l` (248 dances in each case; this is used nowhere, and the code is `gate/remark2/`, §12.1):
- random payments `p(d) = 4q(d)`, `q(d) ∈ [−9, 9]` non-zero, and `u = 1`: three dances are not clean, all at `l = 63`;
- the payments `4(d + c)`, `c = 1, …, 4`, and random odd `u(d) ∈ [−17, 19]`: 79 dances are not clean, the first at `l = 32`.

With the coefficients `η_m` of `Ψ_0` in place of the random `ζ_m`, all 496 dances are clean.

### 10.6 The odd families

**Theorem 10.16.** Let `α ≥ 2`, `c ≥ 0`, `η ∈ A` a unit, `ζ_m ∈ ℤ_2` constants and `Ξ := 2^α(D + c) + ηF + Σ_{m≥2} ζ_m F^{(m)}`. Then for every `l ≥ 0`, **`coker(Ξ on T(l)) ≅ X^{(α)}(l, c)`.**

*Proof.* For `c ≥ 1`: Theorems 10.15 and 10.12. For `c = 0`, let `Ξ_c` and `Σ'_c := 2^α(D + c) + ηF` be the operators with the shift `c ∈ ℤ_2`. By Theorem 10.15 their dances are clean for every `c ∈ ℤ_2`, and the entries of their final matrices are continuous functions of `c`: each level is obtained from the previous one by ring operations, odd denominators, the inversion of a pivot whose diagonal constant term is a unit, and a division by `2` that stays integral. For `c = 2^n`, `n ≥ 0`, Theorem 10.12 gives `M_w(Ξ_c) − M_w(Σ'_c) = M_w(Σ'_c) ∘ E'_c` with `v_2(E'_c) ≥ 1`, that is: for every entry, `v_2(M_w(Ξ_c) − M_w(Σ'_c)) ≥ v_2(M_w(Σ'_c)) + 1` (both sides `∞` if the entry of `M_w(Σ'_c)` is `0`). Let `n → ∞`. Where `M_w(Σ'_0)` has a non-zero entry, its valuation is that of `M_w(Σ'_{2^n})` for large `n`, and the inequality passes to the limit. Where it has a zero entry, `v_2(M_w(Σ'_{2^n})) → ∞`, hence `v_2(M_w(Ξ_{2^n})) → ∞` and the entry of `M_w(Ξ_0)` is `0`. So `M_w(Ξ_0)` has the support and the entry valuations of `M_w(Σ'_0)`, which are those of `M^{(α)}(l, 0)` (Lemma 10.6 and Theorem D). Theorem 7.10 at the shift `0` uses only these data, so the Smith forms agree, and the cokernels follow from Proposition 10.7. ∎

**Corollary 10.17 (the fold law on the odd families).** For every `l ≥ 0` and every `j ≥ 0`,
  **`X̄(2l + 1, j) ≅ 2X(2l + 1, j)`.**

*Proof.* Let `c = ⌈j/2⌉`. By §10.2, `Ψ_j = 4(D + c) + η F + Σ_{m≥2} η_m F^{(m)}` with constant integral `η_m` and `η = η_1` a unit (`1` for even `j`, `1/3` for odd `j`). By Theorem 10.16 (`α = 2`), `coker(Ψ_j on T(l)) ≅ X^{(2)}(l, c) = coker(Σ_c on T(l))`. Lemma 10.4 identifies the two sides with `X̄(2l + 1, j)` and `2X(2l + 1, j)`. ∎

### 10.7 The even families

Lemma 10.5 presents both sides of an even family as glued systems of size `2` on `N = T(l)`. Their arms are odd-family operators, which differ by multiples of `2`. Two facts make the glue harmless: the dance modulo `2` sees only the operator modulo `2` (Lemma 10.18), and gluing commutes with the dance (Lemma 10.19). Then the second side differs from the first by a unit at the bottom of the dance (Lemma 10.20).

Fix the shift `c ∈ ℤ_2` used for the positions, and let `𝔞: 𝒦 → ℤ_2`, `a + 2χ(2y) ↦ a`. It is a ring homomorphism, and `𝔞(ϑ(· − e)) = 𝔞(ϑ) + 2χ(−2e) ≡ 𝔞(ϑ) (mod 4)`. So `𝔞` modulo `4` is a shift-invariant ring homomorphism; exactly as in Lemma 10.14, it induces a ring homomorphism from `𝒯_h` to the commutative ring `R_{ℤ/4} := (ℤ/4)[F^{(m)}][E_t]/(E_t^2)`. By Lemma 10.13(c), every value `ϑ(y)` is `≡ 𝔞(ϑ) (mod 4)`.

**Lemma 10.18 (modulo 2).** Let `G, G' ∈ 𝒯_0` both satisfy (a) and (b) of Theorem 10.15, and suppose `G ≡ G' (mod 2)` (every coefficient, at every position). Then **`G_h ≡ G'_h (mod 2)` at every level `h`.**

*Proof.* By induction it suffices to treat one twist move (a `V`-split does not change the congruence). By Theorem 10.15, `S ∈ 2𝒯`, so `𝔞(G_{h+1}) = 𝔞(S)/2`, and `G_{h+1}` modulo `2` is determined by `𝔞(S)` modulo `4`. In `R_{ℤ/4}`,
  `𝔞(S) ≡ 𝔞(Dd) − β^2 π^{−1}`,  `β := 𝔞(B) ≡ 𝔞(C)`,  `π := 𝔞(P)`,
because the shift `2^h` between `B` and `C` is invisible modulo `4`. Now pass from `G_h` to `G'_h`, whose `𝔞`-image differs by `2δ`. Then `𝔞(Dd)` changes by a multiple of `4` (the factor `2q + 2`). Next, `β` changes to `β + 2δ'` and `β^2` by `4βδ' + 4δ'^2 ≡ 0` (commutativity). The inverse `π^{−1}` changes by `−2π^{−2}δ'' (mod 4)`, so `β^2π^{−1}` changes by `−2β^2π^{−2}δ''`, which is `≡ 0 (mod 4)` because `β^2 ≡ 0 (mod 2)`: modulo `2`, `β^2` is the square of the constant term of `β`, that is of a payment, which is even. So `𝔞(S') ≡ 𝔞(S) (mod 4)`, and `G'_{h+1} ≡ G_{h+1} (mod 2)`. ∎

**Lemma 10.19 (the glue).** Let `X, Y` be systems of size `1` on `T(l)` whose dances along `w` are clean, with `X_h ≡ Y_h (mod 2)` at every level `h`. Then the dance of `glue(X, Y)` is clean, **`glue(X, Y)_h = glue(X_h, Y_h)` at every level**, and in particular `M_w(glue(X, Y)) = glue(M_w(X), M_w(Y))`.

*Proof.* `glue(X, Y) = L^{−1} diag(X, Y) L` with the scalar matrix `L = [[1, 0], [1/2, 1]]`, which acts on the outer slot. Every move acts slot by slot on the inner structure, so the move of `L^{−1}ZL` is `L^{−1}` times the move of `Z` times `L`: the pivot, the other blocks and the Schur complement are conjugated by `L`. For `Z = diag(X, Y)` the dance is the two dances side by side. So `glue(X, Y)_h = glue(X_h, Y_h)` as rational systems. A glued system `glue(U, U')` is integral if and only if `U ≡ U' (mod 2)`; its pivot `glue(P_U, P_{U'})` is then invertible over `ℤ_2`; and its Schur complement `glue(S_U, S_{U'})` is `≡ 0 (mod 2)` if and only if `S_U ≡ S_{U'} ≡ 0 (mod 2)` and `S_U ≡ S_{U'} (mod 4)`, that is `U_{h+1} ≡ U'_{h+1} (mod 2)`. ∎

**Lemma 10.20 (the bend).** Let `c ≥ 1`, `Ψ := 4(D + c) + ηF + Σ_{m≥2} ζ_m F^{(m)}` (`η` a unit, `ζ_m ∈ ℤ_2` constants), `Σ := 4(D + c) + ηF`, and
  `N_± := 2^k·out (Ψ ± 2)^{−1} in`,
with the maps `out = out_k`, `in = in_k` of Lemma 10.8 (`Ψ ± 2` is invertible: its payments `4(d + c) ± 2` never vanish). Then **`M_w(Ψ)·N_± ∈ 2·Mat(ℤ_2)`.**

*Proof.* Put `w(d) := v_2(4(d + c)) − 1 = 1 + v_2(d + c) ≥ 1` and `W[a, b] := Σ_{d=a}^{b} w(d)`. As in Corollary 10.9, `(N_±)_{YX} = (M_w(Σ)^{−1})_{YX}·R_{YX}`, where `R_{YX} = y^{Ψ±2}_L(f)/y^{Σ}_L(f)` on the window `[o_X, o_Y + K − 1]`. Expand `y^{Ψ±2}` as in Lemma 10.10. A composition, divided by the main term of `y^Σ`, is
  `± (∏_i ζ_{m_i}·η^{−L}/∏_i m_i!) · ∏_{landed} π(d)/(π(d) ± 2) · ∏_{skipped} π(d)`,  `π(d) = 4(d + c)`.
Here `v_2(π(d)/(π(d) ± 2)) = w(d)`, `v_2(π(d)) = w(d) + 1`, and `−Σ_i v_2(m_i!) ≥ −s'`, where `s'` is the number of skipped floors. So `v_2(R_{YX}) ≥ W[o_X, o_Y + K − 1]`. By Theorem 10.12, `M_w(Ψ) = M_w(Σ) ∘ (1 + E')`, and `M_w(Σ) = 𝔡_1 𝒜 𝔡_2` with `v_2((𝔡_1)_D) = −W[0, o_D − 1] + c_0`, `c_0` independent of `D` (as `v_2(π(d)) = w(d) + 1`). Each term of `(M_w(Ψ) N_±)_{DX} = Σ_Y M_w(Ψ)_{DY}(N_±)_{YX}` is non-zero only for `X ⊆ Y ⊆ D`, and then has valuation at least
  `v_2((𝔡_1)_D) − v_2((𝔡_1)_X) + δ(D ∖ Y) + δ(Y ∖ X) + W[o_X, o_Y + K − 1]`
  `= δ(D ∖ Y) + δ(Y ∖ X) + W[o_D, o_Y + K − 1] ≥ 1`,
because `o_D − o_Y = o_{D∖Y} ≤ K − 1`, so the window `[o_D, o_Y + K − 1]` is non-empty and `w ≥ 1` on it. (`(𝔡_2)_Y` cancels, and `v_2((𝒜^{−1})_{YX}) ≥ δ(Y ∖ X)`, proof of Lemma 10.11.) ∎

**Corollary 10.21.** In Lemma 10.20, the dances of `Ψ(Ψ ± 2)/2` are clean, and
  **`M_w(Ψ(Ψ + 2)/2) = W_+·M_w(Ψ)`,  `M_w(Ψ(Ψ − 2)/2) = W_−·M_w(Ψ)`,  `W_± ∈ ±I + 2·Mat(ℤ_2)`.**

*Proof.* *Cleanliness.* `Ψ ∈ 𝒯_0` with (a), (b). By Lemma 10.14, `Θ(Ψ^2) = Θ(Ψ)^2 = Θ(4y)^2 = 0` and `Θ(2Ψ) = 0`, so `Ψ(Ψ ± 2) ∈ 2𝒯_0` and `Ψ(Ψ ± 2)/2 ∈ 𝒯_0`. Its payment is `4y(4y ± 2)/2 = 4y(2y ± 1) = 2χ(2y)` with `χ = X^2 ± X`, which is `≡ 0 (mod 4)`. Its coefficient of `F` is `(η·4(y − 1) + 4y·η ± 2η)/2 = η(4y − 2 ± 1)`, which is odd. Theorem 10.15 applies. *The identity.* By partial fractions (all operators are series in `F` and `D`, and `Ψ`, `Ψ ± 2` commute), `(Ψ(Ψ + 2)/2)^{−1} = Ψ^{−1} − (Ψ + 2)^{−1}` and `(Ψ(Ψ − 2)/2)^{−1} = (Ψ − 2)^{−1} − Ψ^{−1}`. By Lemma 10.8 applied to the clean dances of `Ψ` and `Ψ(Ψ ± 2)/2` (same `out`, `in`):
  `M_w(Ψ(Ψ + 2)/2)^{−1} = M_w(Ψ)^{−1} − N_+ = M_w(Ψ)^{−1}(I − M_w(Ψ)N_+)`,
so `W_+ = (I − M_w(Ψ)N_+)^{−1}`. Likewise `W_− = −(I − M_w(Ψ)N_−)^{−1}`. By Lemma 10.20, `W_± ≡ ±I (mod 2)`. ∎

**Theorem 10.22 (the fold law on the even families).** For every `l ≥ 0` and every `i ≥ 0`,
  **`X̄(2l + 2, i) ≅ 2X(2l + 2, i)`.**

*Proof.* Let `Y_0 := 1 + (−1)^i Sh^{−1}`, so that `Ψ_{i+1} = Ψ_i + 2Y_0` (§10.2). Take the positions `y = f + ⌈i/2⌉` at level `0`. In these positions both `Ψ_i` and `Ψ_{i+1}` lie in `𝒯_0` with (a) and (b): their payments are `4y` and `4(y + [i even])`, their coefficients of `F` are the units `1`, `1/3`, and their other coefficients are constants.
*The arms are congruent.* `Ψ_{i+1} − Ψ_i = 2Y_0 ≡ 0 (mod 2)`. For the second side put `U := Ψ_{i+1}(Ψ_{i+1} − 2)/2` and `U' := Ψ_i(Ψ_i + 2)/2`, both in `𝒯_0` with (a) and (b) (proof of Corollary 10.21). With `Ψ := Ψ_i`,
  `U − U' = ΨY_0 + Y_0Ψ − 2Ψ + 2Y_0^2 − 2Y_0 ≡ [Ψ, Y_0] = 4[D, Y_0] ≡ 0 (mod 2)`,
because `Y_0` and the `F`-part of `Ψ` are power series in `F` with constant coefficients and commute, while `Ψ` contains `4D`. (`Ψ_i` and `Y_0` do not commute, so the product `(Ψ_{i+1} + Ψ_i)(Y_0 − 1)` is not the difference.)
*The case `i ≥ 1`.* By Lemma 10.18 the arms dance congruently modulo `2`, so by Lemma 10.19 the dances of `glue(Ψ_{i+1}, Ψ_i)` and `glue(U, U')` are clean, and by Corollary 10.21 (with `Ψ_{i+1}` and `Ψ_i`, whose shifts `⌈(i + 1)/2⌉`, `⌈i/2⌉` are `≥ 1`)
  `M_w(glue(U, U')) = glue(W_− M_w(Ψ_{i+1}), W_+ M_w(Ψ_i)) = glue(W_−, W_+)·M_w(glue(Ψ_{i+1}, Ψ_i))`,
since `glue(X, Y)·glue(X', Y') = glue(XX', YY')`. Now `glue(W_−, W_+) = [[W_−, 0], [(W_+ − W_−)/2, W_+]]` is integral (`W_+ ≡ I` and `W_− ≡ −I (mod 2)`, so `W_+ − W_− ∈ 2·Mat(ℤ_2)`) and has invertible diagonal blocks, so it lies in `GL(ℤ_2)`. The two final matrices are associates and have the same Smith form; Proposition 10.7 and Lemma 10.5 give `X̄(2l + 2, i) ≅ 2X(2l + 2, i)`.
*The case `i = 0`.* Then `Ψ_0 = 4D + u·tanh(u/2)` is not invertible. Replace the shift by a parameter: `i = 2c`, `c ∈ ℤ_2`, with payments `4(D + c)` for `Ψ_i` and `4(D + c + 1)` for `Ψ_{i+1}`. Every object above is continuous in `c`: the dances are clean for every `c` (Theorem 10.15 and Lemmas 10.18 and 10.19); `N_+` uses `(Ψ_i + 2)^{−1}`, whose payments `4(d + c) + 2` never vanish, and `N_−` uses `(Ψ_{i+1} − 2)^{−1}`, with payments `4(d + c + 1) − 2`. For `c = 2^n`, `n ≥ 0`, we have `M_w(Ψ_i)N_+ ∈ 2·Mat`, `M_w(Ψ_{i+1})N_− ∈ 2·Mat`, and the identity
  `M_w(glue(U, U')) = glue(W_−, W_+)·M_w(glue(Ψ_{i+1}, Ψ_i))`,
with `W_± = ±(I − M_w(·)N_±)^{−1}`. The set `2·Mat(ℤ_2)` is closed, so at `c = 0` the products `M_w(Ψ_0)N_+` and `M_w(Ψ_1)N_−` still lie in `2·Mat`; then `W_±` are defined and `≡ ±I (mod 2)` there, and the identity passes to the limit. So the final matrices are associates at `c = 0` as well. ∎

### 10.8 Proof of Theorem DW, and the folded cube

*Proof of Theorem DW.* By Proposition 10.3 it suffices that `X̄(λ, i) ≅ 2X(λ, i)` for every `λ ≥ 1` and every `i ≥ 0`. For `λ = 2l + 1` this is Corollary 10.17, and for `λ = 2l + 2` Theorem 10.22. ∎

*Proof of Corollary 1.4.* The `2`-part is Theorem DW: `Syl_2 K̄(n) ≅ 2·Syl_2 K(Q_n)` is `Syl_2 K(Q_n)` with every exponent lowered by one, the `a_n` factors `ℤ/2` disappearing (Corollary 1.5). The odd part is given by [GMMY24, Proposition 1.9]. ∎

**The mod-2 layer.** Let `L̄` be the Laplacian of the folded cube, a square matrix of size `2^{n−1}` (`n ≥ 2`), with `coker L̄ ≅ ℤ ⊕ K̄(n)`. Its invariant factors divisible by `2` are the zero one and one for each cyclic factor of `Syl_2 K̄(n)`. By Corollary 1.5, `Syl_2 K(Q_n)` has `2^{n−1} − 1` cyclic factors, of which `a_n` are `ℤ/2`; by Theorem DW, `Syl_2 K̄(n)` has `2^{n−1} − 1 − a_n`. So `rank_{𝔽_2} L̄ = 2^{n−1} − (2^{n−1} − a_n) = a_n`. This is [GMMY24, Proposition 2.12] (with their `r = n − 1`). Their Remark 2.13 asks whether its coincidence with Bai's count of the factors `ℤ/2` of `K(Q_n)` is a «special case of some deeper connection». Theorem DW is such a connection: the coincidence is its first layer.

**Remark (what the fold sees).** The proof uses the antipode `a = x_1⋯x_n` through Lemma 10.1 only: `a` is `(−1)^{(n−H)/2} exp(F)`, an operator built from the weight and the divided powers of `F`, so it is carried by the family decomposition of Theorem 3.6. An element such as `x_1x_2` acts on two tensor factors only; it is not of this kind, and the quotient by it does not halve the group (we checked `3 ≤ n ≤ 12`, §12).

## 11. Open questions

1. **Other quotients of the cube.** The Cayley graphs of `𝔽_2^r` are the quotients of cubes by binary linear codes [IKKY23, Proposition 37], and those containing `𝟙` — the «non-generic» ones in the sense of [GMMY24], see also [Yue24] — are built from the folded cube by successive quotients of codimension one [GMMY24, §2.2]. Does the method of §10 compute their `2`-parts? The antipode was special because it is `±exp(F)` on every family (Lemma 10.1); a general code element acts on some tensor factors only.
2. **The turned lid.** Write `C_b := Q_b/⟨𝟙⟩` (so `C_1` is a point). For `a + b = n`, the graph `Q_a □ C_b` is the quotient of `Q_n` by a translation of weight `b`. We measured, for every `n ≤ 12` and every `b`, that **`Syl_2 K(Q_a □ C_b) ≅ Syl_2 K(Q_b □ C_a)`**, although the graphs are not isomorphic and the odd parts differ; and that `2·Syl_2 K(Q_n) ≅ Syl_2 K(Q_a □ C_b)` holds only for `b = n` (Theorem DW). Theorem DW is the degenerate end of this symmetry (the twin of `b = n` would be the quotient by `0`). We have no proof.
3. **A direct proof of the fold law.** Reiner and Tseng give an exact sequence `0 → K(G^±) → K(Q_n) → K̄(n) → 0` for the double cover `Q_n → Q_n/⟨𝟙⟩` (`n ≥ 3`), with `K(G^±)` the critical group of a signed graph [RT14]. Theorem DW identifies the `2`-part of the target, abstractly, with `2·Syl_2 K(Q_n)`. Is there a proof through the signed graph, without tilting modules?
4. **The meaning of pooling.** The integer antitonic fit appears because the Smith form of `M(λ, i)` is governed by the cheapest matchings of a triangular cost matrix (§6–§7). Is there a module-theoretic reason, such as a filtration of `X(λ, i)` whose layers are the pooled blocks?
5. **Other primes and other graphs.** For the Hamming graphs `H(n, p)`, `p` odd, the group ring `ℤ[(ℤ/p)^n]` is the `n`-th tensor power of `ℤ[ℤ/p]`, and the Laplacian is again a sum over the tensor factors. Is there a decomposition of their `p`-parts over tilting modules of a suitable group in characteristic `p`?
6. **Formal verification.** No part of this paper has been checked by a proof assistant. The dance (§4, §10.3) and the valuation arguments (§5–§7) are finite and explicit, and seem suited to it.

## 12. Computations

### 12.1 The checks published with this paper

All the checks below were run on a laptop, under a watchdog with limits on memory and time; a log counts only if it ends with the watchdog's final line. The code is in the folder `gate/` that accompanies this paper. A **control** is a deliberately wrong variant that must fail; «none» means that the row has no control.

| statement, and the code that checks it | range | result | control |
|---|---|---|---|
| Main Theorem against the direct `2`-adic Smith form of the Laplacian of `Q_n`; Theorem DW against that of `Q_n/⟨𝟙⟩`; code `gate_direct.py` | `n = 2, …, 11` | 10/10 and 10/10 | the rule without pooling fails at `n = 6, 10`; the rule without the term `h(D)` at `n = 2` and `4, …, 11`; `Q_n/⟨x_1x_2⟩` in place of the folded cube fails for every `n = 3, …, 11` |
| Theorem D: direct Smith form of `σ^{(α)}_i` on `T(λ)` against small clocks `⊕ coker(2^k M)`; Theorem 4.4 against the dance; code `gate_dance.py` | `λ ≤ 40`, `α = 1, 2`, `i ≤ 6`, `dim T(λ) ≤ 64` | 432/432; 0 mismatches | the closed form without the factor `2^{o(Δ)}` differs from the dance in 420/420 cells, and predicts a wrong Smith form in 262 |
| Propositions 5.2 · 5.3 · 5.4 (5.2 against the closed form of Theorem 4.4; of 5.4, the formula for the clocks `u_0(D)`, `D ≠ ∅`); code `gate_sections5to7.py` | `λ < 64`; `i = 1, …, 40` (`α = 1, 2` for 5.2, `α = 1` for 5.3); `i = 0`, `α = 1` for 5.4 | 109 200 matrix entries · 14 560 clocks · 301 clocks, 0 failures | none |
| Theorem 7.10: Smith form of `M` against the pooled clocks; code `gate_sections5to7.py` | `λ < 64`, `i ≤ 12`, `α = 1, 2` | 1 638 cells, 0 failures | the raw clocks, without pooling, are rejected in all 322 cells where pooling changes them |
| Theorem 7.8: the construction of `V` and the claims of its proof, for three admissible prices `c_F`; code `gate_sections5to7.py` | houses with `I ≠ ∅` and `k ≤ 6` (`λ ≤ 126`), `α ≤ 3`, every `ℓ` | 16 002 houses, 48 006 house-checks, 0 failures | without gold, (G) fails in 164 houses (`λ < 64`, `α = 1`); with `c_F := v'(I')`, in 24 |
| Theorem 7.8, strict (Cut); Lemma 7.2(b) where it is applied: the penalty shifts `P_r, P_c ≤ 4` and the deletion at `i = 0`; code `gate_strict_cut.py` | every house with `1 ≤ k ≤ 6`, `α ≤ 3` | 16 380 houses, 8 001 boundaries, 192 024 non-zero shifts (24 on each house with a boundary), 360 deletions, 0 failures | strictness tested one dancer after the boundary fails in 1 911 of 7 038 houses; the shift moved one dancer late breaks the integer shift in 18 606 of 192 024 |
| Lemma 7.9: the fit of `x_H`, of its shifts and of its deletions is integral; code `gate_strict_cut.py` | the same | 0 non-integral values | `x_H` with `1` added at its first dancer (not a house) has a non-integral fit in 1 942 houses |
| Lemma 7.2(b) on random sequences; code `gate_lemma72.py` | 20 000 sequences of length `≤ 9` | 0 failures | jumps of `δ` at cuts that are not strict break the integer part in 189 of 2 841 trials |
| Theorem 6.2: exactly one golden bijection; code `gate_theoremO.py` | `|I| ≤ 5`, every `r` | 69 cases, 0 failures | «golden» replaced by «any subset» or by «any run of digits»: the count is not `1` in 42 and in 26 cases |
| Corollary 1.5 · Lemma 9.7 · Corollary 1.6; code `gate_section9.py` | `n ≤ 200` | 199 · 199 · 197 values, 0 failures | none (a counter shows that `c_n = G` fails for 37 values of `n`) |
| Propositions 9.3 · 9.4 · 9.6; code `gate_section9.py` | `λ ≤ 300` | 300 · 292 · 22 500 cells, 0 failures | none (a counter shows that the bound `g(n − i)` is exceeded in 298 cells) |
| Corollary 1.7; code `gate_section9.py` | `e = 1, …, 8` | 8/8 | none |
| the weights `η_m`, `η'_m` of §10.2: the Bernoulli formulas, and `v_2 = 0`; code `gate_section10.py` | `m ≤ 39` | 0 failures | none |
| Lemma 10.1 on `V^{⊗n}`; code `gate_section10.py` | `n ≤ 6` | 0 failures | none |
| Lemmas 10.4 and 10.5, both sides, and `X̄(λ, i) ≅ 2X(λ, i)`, on the lattices `T(λ)` of §3.3; code `gate_section10.py` | `λ ≤ 22`, `i ≤ 5` | 66 + 66 + 66 + 66 and 132/132 | the sign-free fold fails in 124/132; a wrong sign in `Ψ_j` fails 66/66 |
| Remark (2) of §10.5 (a measurement); code `gate_remark2.py`, in `remark2/` | `l = 2, …, 63`, seed `11` | as stated there | none |

The folder `remark2/` contains three engines of the project, copied unchanged, and the driver that sets the four experiments of the remark. The direct computations of the first row also give the example of §1.3: `Syl_2 K(Q_5) = {1: 6, 3: 4, 4: 1, 6: 4}` and `Syl_2 K̄(5) = {2: 4, 3: 1, 5: 4}`.

### 12.2 Independent re-computations

Six readers of the project (Appendix A) recomputed what follows, each with code of its own, never the authors'. Their code and logs are part of the project's record. As in §12.1, «none» means that the row has no control; «fires» means that the reader's control failed, as it must.

| statement | reader | range | result | control |
|---|---|---|---|---|
| Main Theorem against the Smith form of the Laplacian of `Q_n` | 1 | `n ≤ 13` | 12/12 | fires |
| Main Theorem, from the rule as printed in §1; Theorem DW | 3 | `n ≤ 12` | 12/12 and 12/12 | the rule without the lowest digit of `I`, `a_n ± 1`, and `Q_n/⟨x_1x_2⟩` fail |
| Theorem DW, in the vertex basis | 2 | `n ≤ 12` | 11/11 | `Q_n/⟨x_1x_2⟩` fails for `n = 3, …, 12` |
| Gao et al.'s Table 1 | 3 | `n = 7, …, 11` | agrees entry by entry | none |
| the recursion of §1.2 against Larsen's fusion rule [Lar24, §2] | 1, 3 | even `n ≤ 64` | 32/32 | fires |
| Theorem 7.8 | 1 | houses with `λ ≤ 255`, `α ≤ 4` | 0 failures | none |
| Theorem 7.8, every claim of its proof, strict (Cut), the integer separation of adjacent level sets (Lemma 7.9 of version 2), the integer shifts | 3 | all houses with `k ≤ 7` (`k = 0` included), `α = 1, 2`, penalties `≤ 6` | 43 690 houses, 0 failures | two wrong prices of the central flat are detected in 2 550 and 2 808 of 3 979 houses |
| Theorems D and 7.10 on the lattices `T(λ)` | 3 | two runs, `λ ≤ 31`, `i ≤ 10` and `λ ≤ 63`, `i ≤ 8`, each with `α = 1, 2`; the 43 and 372 cells whose predicted exponent is at least 60 skipped | 639 and 762 cells compared, 0 failures | the raw clocks are rejected in all 102 and 172 compared cells where pooling acts |
| Theorem 7.10 on the matrices `M` | 3 | `λ ≤ 127`, `i ≤ 30`, `α = 1, 2` | 7 874 cells, 0 failures | the raw clocks are rejected in all 1 876 cells where pooling acts |
| Theorem 7.8, strict (Cut), the integer separation of adjacent level sets (Lemma 7.9 of version 2), the penalty shifts `P_r, P_c ≤ 4` and the deletion at `i = 0` | 4 | every house with `1 ≤ k ≤ 7`, `α ≤ 3` | 65 532 houses, 777 240 non-zero shifts, 741 deletions, 0 failures | a price of the central flat one above or one below the interval fails in 10 374 houses each; the shift one dancer late fails in 78 070 of 721 872; strictness one dancer after the boundary fails in 7 967 of 30 078 |
| Theorem 7.10 on the matrices `M` | 4 | `λ ≤ 127`, `i ≤ 30`, `α = 1, 2` | 7 874 cells, 0 failures | the raw clocks are rejected in all 1 834 cells with `i ≥ 1` where pooling acts; the penalty one dancer late in all 1 904 |
| Lemma 7.2(b), restated, on random sequences | 4 | 50 000 sequences of length `≤ 10` | 0 failures | a jump at a cut that is not strict breaks the integer part in 736 of 9 939 trials |
| Lemma 7.9 (integrality) | 4 | every house with `1 ≤ k ≤ 7`, `α ≤ 3`, and the 7 634 cells of its row on the matrices `M` other than the 240 with `i = 0` and `I ≠ ∅` (the 7 620 with `i ≥ 1`, and the 14 with `i = 0` and `I = ∅`, where `M = 0`) | no non-integral level set | none |
| Lemma 7.9; the strict (Cut); Lemma 7.2(b) at the penalty shifts; the deletion at `i = 0` | 5 | every house with `1 ≤ k ≤ 7`, `α ≤ 3` (65 532); penalties `P_r, P_c ≤ 4` on the 8 001 houses with `k ≤ 6` that have a boundary (192 024 cells); 741 deletions | 0 failures | `x_H` with `1` added at its first dancer: non-integral in 1 942 of 16 380 houses; strictness one dancer after the boundary fails in 7 967 of 30 078 |
| §1.2 (the rounding never acts); Propositions 5.3, 5.4 and Lemma 7.5; Proposition 9.6 (H) | 5 | every family `λ ≤ 255`, every shift `i ≤ 40` (10 455 cells; (H) on the 10 200 with `i ≥ 1`) | 0 failures | for the integrality: the raw clocks with `1` added at the first dancer have a non-integral block mean in 2 316 of the 9 880 cells with `I ≠ ∅` and `i ≥ 1`; none for Propositions 5.3 and 5.4, Lemma 7.5 and (H) |
| Theorem 6.2 | 3 | `|I| ≤ 5` | 69/69 | «any run» and «any subset» fail in 26 and 42 cases |
| Corollaries 1.5, 1.6 (from the rule) and 1.7 | 3 | `n ≤ 300`; `e ≤ 8` | 0 failures | a wrong exponent in Corollary 1.5 and a wrong constant in Corollary 1.6 fail for 149 and 65 values of `n` |
| odd part of Corollary 1.4 | 3 | `p = 3, 5, 7`, `n ≤ 11` | 30/30 | fires |
| `X̄(λ, i) ≅ 2X(λ, i)` on explicit lattices | 2 | `λ ≤ 20`, `i ≤ 6` | 140/140 | `λ = 0` and the sign-free fold fail |
| `X̄(λ, i) ≅ 2X(λ, i)` from the definition `T(λ)/(τ_iT(λ) + (a − 1)T(λ))` | 3 | `λ ≤ 63`, `i ≤ 8` | 513/513 | `a` replaced by `−a` fails 513/513 |
| the formal dance of `Ψ_j`: clean, with the support, the entry valuations and the Smith form of `M^{(2)}(l, ⌈j/2⌉)` (Theorems 10.12, 10.15, 10.16) | 3 | `l ≤ 31`, `j ≤ 7` | 256/256 | `α = 1`, and a coefficient of `F^{(2)}` depending on the parity of the floor, fail |
| Theorem 10.15: one move on random covariant systems | 2 | levels `0`–`3`, `1`–`4` dancers | 800/800 | none |
| Lemma 10.20 | 2 | `l ≤ 24`, `c = 1, …, 4`, three kinds of weights | 96/96 for each kind and sign | `α = 1` and `Ψ ± 4` fail in 95/96 and 71/72 |
| the turned lid (§11, question 2) | 3 | `n = 3, …, 12`, every `b` | 0 failures (a measurement) | none |
| the cells of the rows of readers 4 and 5; Lemma 7.9 on houses and on the 10 455 cells of the fifth reader's second row | 6 | `λ ≤ 127`, `i ≤ 30`, `α = 1, 2`; houses with `1 ≤ k ≤ 6`, `α ≤ 3`; `λ ≤ 255`, `i ≤ 40` | 7 874 cells: 254 with `i = 0` (240 with `I ≠ ∅`), 7 620 with `i ≥ 1`; 16 380 houses and 10 455 cells, no non-integral fit | the controls of reader 5 reproduced: 1 942 of 16 380 houses, 2 316 of 9 880 cells |

## 13. Exact status

- **Proved, with the grade «pencil, audited, read cold»:** the Main Theorem; Theorem D; Theorems O and F; Theorem DW and Corollary 1.4; Corollaries 1.5, 1.6 and 1.7. Their proofs were read cold as text in version 1, which had one gap (Lemma 7.2(b)); the repair of version 2 (the restated Lemma 7.2(b), the strict (Cut) of Theorem 7.8, and their uses in Theorem 7.10 and Proposition 9.6) was read cold in its turn; and the changes of version 3, among them Lemma 7.9, on which the printed proof of the Main Theorem now rests (§8, Theorem 7.10), were read cold by a fifth reader, the changes of version 4 by a sixth, the changes of version 5 by a seventh, and the changes of version 6, with its whole pdf, by an eighth (Appendix A).
- **Added in version 3, audited, read cold:** Lemma 7.9 in its new form (integrality of the fit), found and proved by the fourth reader, re-proved by the auditor, and re-derived by the fifth reader. Version 2 added the strictness of the cuts to the (Cut) of Theorem 7.8 and restated Lemma 7.2(b); version 3 strengthened Lemma 7.9, added the hypothesis «even» to Lemma 10.6(a), and added the explicit quantifier «for every `L ≥ 0` and every floor `f`» to Lemma 10.10; no other numbered statement changed in versions 2 to 7.
- **Changed in version 4, audited, read cold:** the corrections of the fifth reading and the typesetting (Appendix A). No mathematical statement changed.
- **Changed in version 5, read cold:** the corrections of the sixth reading and the typesetting (Appendix A). No mathematical statement changed.
- **Changed in version 6, read cold:** the corrections of the seventh reading (Appendix A). No mathematical statement changed.
- **Changed in version 7, made by the auditor, not yet read cold:** the corrections of the eighth reading (Appendix A). No mathematical statement changed.
- **Measured, not proved:** the turned lid (§11, question 2), and the measurements of Remark (2) of §10.5.
- **Not done:** a cold reading of the changes of version 7; a human referee; a formal verification.

No human expert has refereed any part of this work. The results are stated as theorems because every step has a written proof that was re-derived by readers other than its author. That is not a substitute for refereeing.

## Acknowledgements and use of AI

The mathematics of this paper was developed with extensive use of Claude, an AI system made by Anthropic, working under the author's direction in separate roles:
- instances that proposed and wrote proofs, each from a written mission;
- instances that re-derived them step by step and ran their own checks;
- instances that read the chains, and then the whole text, cold, with no access to the audits (Appendix A).

The author directed the project and takes responsibility for the content.

The work took five days, from 2 to 6 October 2026. It began on 2 October 2026 as a search, inside another project of the author, for open problems within reach of the same methods. The full record — the missions, the reports, the audits, the cold readings, the engines and their logs, including the routes that failed — is kept with the project and is available from the author.

## Appendix A. How this work was done

**Writing and checking.** The proofs were found, family of statements by family of statements, by separate instances of an AI system working as **constructors**, each from a written mission and in a folder of its own («flights» 1 to 9, 3–5 October 2026). Each flight was then **audited** by a different instance, which re-derived every step in its own words, marked it CORRECT, GAP or ERROR, and ran its own engines (never the constructor's) with controls built to fail. A step went into the chain only after the audit. The chains and then the text were read by **cold readers**: further instances that never saw the audits, and wrote their own verdicts and their own code. Every computation ran under a watchdog with limits on memory and time, and every log is checked for its final line.

**Readings.**
- **The Main Theorem** (flights 1–4: Theorems D, O, U, F and the integer fit). Audited flight by flight. Read cold on 4 October (cold reader 1), from the statements and the flights' reports, with no access to the audits: **«holds»**, every link re-derived, with three remarks on presentation, applied in version 1.
- **Corollaries 1.5–1.7** (flights 5–6). Audited, with the auditor's own gates; read cold numerically by cold reader 1 (`n ≤ 64`), and as text with version 1 (below).
- **Theorem DW** (flights 6–9). Audited flight by flight. Read cold on 5 October (cold reader 2), with no access to the audits: **«holds»**, with six remarks on presentation and a priority search, applied in version 1.
- **Version 1 of this text** was written by the auditor from the flights, the audits and the readings. Two parts were new in the writing: the proof of Theorem 6.2 by top bits, and the organization of §10 around Theorems 10.12 and 10.15. It was read cold as a whole on 5 October 2026 (cold reader 3) by a reader with no access to the flights, the audits or the earlier readings, who re-derived every numbered statement and wrote its own code: **«holds with gaps»**. It found one gap: the integer part of Lemma 7.2(b) is false as stated (the example in its proof), and it was used in Theorem 7.8 (step 1), Lemma 7.9, Theorem 7.10 and Proposition 9.6. No theorem is affected. Version 2 restates Lemma 7.2(b), adds strict (Cut) to Theorem 7.8 with its proof, and cites it at each use; this repair is the reader's, re-derived by the auditor and checked by machine (§12.1). The reader also found that Remark (2) of §10.5 stated more than had been measured, that the quotation of [Aky26] had been trimmed so as to change its meaning, that four entries of the verification record said more than the code did (the range of Theorem 6.2, the houses of Theorem 7.8 counted as house-checks, a control announced and not implemented in `gate_dance.py`, and rows resting on code not printed), and about thirty points of presentation; all are corrected in version 2.
- **Version 2** repaired the gap. Its changes were read cold on 5 October 2026 (cold reader 4) by a reader with no access to the flights, the audits or the earlier readings, who re-derived every changed step, checked the repair on every house with `1 ≤ k ≤ 7`, `α ≤ 3` and against the Smith form of `M` in 7 874 cells, and wrote its own code: the repair **holds**. It found one false sentence (Remark (2) of §10.5 said «every payment system» where Proposition 4.1 needs an even one; the author then found the same word missing in Lemma 10.6(a), harmless because its only use is for an even system), two rows of §12.1 that said more than their code (zero shifts counted as shifts, and a range wider than the one run), a control that did not control the house check, and points of presentation, the main one being that the cases of the proof of Theorem 7.8 ran together in the pdf. It also found, with a two-line proof, that the fit of every house is integral, so the rounding of the integer fit never acts in this paper: the gap of version 1 was a gap of proof, never of conclusion.
- **Version 3** states that integrality as Lemma 7.9, makes all the corrections above, gives the gates of §7 house-level controls that can fail and runs Theorem 7.10 on the whole printed range (§12.1), and keeps the mathematics of the repair of version 2 as it was read, with the clarifications listed above. Every number printed in it was checked against an engine (§12), but three ranges were printed wider or vaguer than the code ran. Its changes were read cold on 5 October 2026 (cold reader 5) by a reader with no access to the flights, the audits or the earlier readings, who re-derived Lemma 7.9 and every place where it is used, wrote a gate of its own (§12.2), reproduced the gates of §7 and looked at every page of the pdf: the changes **hold**, with no gap and no error. It found points of presentation (where strictness is used after Lemma 7.9, three citations, four sentences of the reading record, one sentence of «Why dance», three ranges of §12) and defects of typesetting: every formula was set in one italic font, scripts were not stacked, and some statements, displays and tables were broken badly across lines and pages.
- **Version 4** made those corrections, except two defects of typesetting (a short page in §1, and a break inside a formula of §10.5), and set the mathematics anew: letters italic, digits, brackets, operators and operator names upright, scripts stacked, displays in display style, and no statement, display, table row or short proof broken across a page (the long tables of §12 run over several pages, row by row, with their header repeated). No mathematical statement changed. The three ranges of §12 were corrected; §12.2 gained the two rows of the fifth reader; and the row of the fourth reader's check of Lemma 7.9 gained a parenthesis, composed by the author and not checked by the fifth reader, which was wrong. Its changes were read cold on 5 October 2026 (cold reader 6) by a reader with no access to the flights, the audits or the earlier readings, who compared every changed passage with version 3 by a script with a control, re-derived every new sentence, re-counted the cells of §12 with its own code, and looked at every page of the pdf: the mathematics of every change **holds**, with no gap and no error. It found one false number (the 7 634 cells of the fourth reader's row are not the cells with `i ≥ 1`: they are the 7 620 with `i ≥ 1` and the 14 with `i = 0` and `I = ∅`), one false sentence (version 3 was still called «this text»), inexact sentences in this record and in §12, points of presentation, and defects of typesetting in 32 kinds: bars and hats placed off their letters, no page numbers, stray bold words, matrices written as lists, breaks inside short formulas, the number sets in italic, the end-of-proof mark from another font, and loose lines.
- **Version 5** makes those corrections and sets the page anew: accents centred over their letters, the number sets in double-struck letters, matrices as matrices, limits under `max` and `min` in displays, enlarged brackets around sums with limits, page numbers, the end-of-proof mark at the right margin, and tables with horizontal rules only. No mathematical statement changed, and no number; the descriptions of four counts of §12 were made exact (the 7 634 cells, the 301 clocks, the 192 024 cells, the 9 880 cells). Its changes were read cold on 6 October 2026 (cold reader 7) by a reader with no access to the flights or the audits, who opened the sixth reading only after writing its verdicts. It compared every changed passage with version 4 by a script with a control, re-counted the numbers of §12 with its own code, and looked at every page of the pdf: the mathematics of every change **holds**, with no gap and no error. It found one false sentence in this record (§13 said that no statement of a theorem had changed in versions 2 to 5, while version 2 added the strict (Cut) to Theorem 7.8), inexact sentences, points of presentation, and defects of typesetting, the main one being that two steps of the proof of Theorem 7.8 had lost their numbers in the pdf.
- **Version 6** makes those corrections. No mathematical statement changed. Its changes, and its whole pdf page by page, were read cold on 6 October 2026 (cold reader 8) by a reader with no access to the flights or the audits, who opened the seventh reading only after writing its verdicts. It compared every change with version 5, re-counted the numbers of §12 with its own code, compared the md and the pdf word by word and number by number, checked every cross-reference and every quotation against its source, and looked at every page: the mathematics of every change **holds**, and nothing on the page is broken. It found two false sentences in this record (the sentence of §13 on what changed in versions 2 to 6, which said «no other statement» and then named three lemmas changed in version 3; and the dates of the work in the Acknowledgements), one row of §12.2 that printed only one of the two ranges its reader ran, and one sentence of §1.7 that could be read as a subtraction.
- **Version 7** (this text) makes those corrections, and says in §12 which ranges of houses include `k = 0`. No mathematical statement changed, and no number. **Its changes have not yet been read cold.**

## References

- [ABERS55] M. Ayer, H. D. Brunk, G. M. Ewing, W. T. Reid, E. Silverman, An empirical distribution function for sampling with incomplete information, *Ann. Math. Statist.* 26 (1955), 641–647.
- [Aky26] T. Akyar, A. Beliakov, K. Delchev, N. Kalinin, E. Lupercio, H. Serrano, M. Shkolnikov, D. Tabares, N. Terekhov, The 2-adic valuation of the order of the all-ones class in the sandpile group of a square, arXiv:2609.10625 (2026).
- [Bai03] H. Bai, On the critical group of the `n`-cube, *Linear Algebra Appl.* 369 (2003), 251–261.
- [BBBB72] R. E. Barlow, D. J. Bartholomew, J. M. Bremner, H. D. Brunk, *Statistical Inference under Order Restrictions*, Wiley, 1972.
- [Bie93] T. Bier, Remarks on recent formulas of Wilson and Frankl, *European J. Combin.* 14 (1993), 1–8.
- [Big99] N. L. Biggs, Chip-firing and the critical group of a graph, *J. Algebraic Combin.* 9 (1999), 25–45.
- [Cla40] T. Clausen, Lehrsatz aus einer Abhandlung über die Bernoullischen Zahlen, *Astron. Nachr.* 17 (1840), 351–352.
- [CSX17] D. B. Chandler, P. Sin, Q. Xiang, The Smith group of the hypercube graph, *Des. Codes Cryptogr.* 84 (2017), 283–294; arXiv:1511.00272.
- [DEGJPP23] J. E. Ducey, L. Engelthaler, J. Gathje, B. Jones, I. Pfaff, J. Plute, Integer diagonal forms for subset intersection relations, arXiv:2310.09227 (2023).
- [DHS18] J. E. Ducey, I. Hill, P. Sin, The critical group of the Kneser graph on 2-subsets of an `n`-element set, *Linear Algebra Appl.* 546 (2018), 154–168; arXiv:1707.09115.
- [DJ14] J. E. Ducey, D. M. Jalil, Integer invariants of abelian Cayley graphs, *Linear Algebra Appl.* 445 (2014), 316–325; arXiv:1308.2335.
- [Don93] S. Donkin, On tilting modules for algebraic groups and finite dimensional algebras, *Math. Z.* 212 (1993), 39–60.
- [EL91] A. El-Amawy, S. Latifi, Properties and performance of folded hypercubes, *IEEE Trans. Parallel Distrib. Syst.* 2 (1991), 31–42.
- [GMMY24] J. Gao, J. Marx-Kuo, V. McDonald, C. H. Yuen, Sandpile groups of Cayley graphs of `𝔽_2^r`, *Comm. Algebra* 52 (2024), 4459–4479; arXiv:1912.06919v3 (cited by its numbering).
- [Hum72] J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Graduate Texts in Mathematics 9, Springer, 1972.
- [IKKY23] K. Iga, C. Klivans, J. Kostiuk, C. H. Yuen, Eigenvalues and critical groups of Adinkras, *Adv. in Appl. Math.* 143 (2023), Paper No. 102450; arXiv:2202.02821.
- [Jan03] J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Mathematical Surveys and Monographs 107, AMS, 2003.
- [Kli18] C. J. Klivans, *The Mathematics of Chip-Firing*, CRC Press, 2018.
- [Kos66] B. Kostant, Groups over `ℤ`, in *Algebraic Groups and Discontinuous Subgroups*, Proc. Sympos. Pure Math. 9, AMS, 1966, 90–98.
- [Kum52] E. E. Kummer, Über die Ergänzungssätze zu den allgemeinen Reciprocitätsgesetzen, *J. Reine Angew. Math.* 44 (1852), 93–146.
- [Lar24] M. Larsen, Bounds for `SL_2`-indecomposables in tensor powers of the natural representation in characteristic 2, arXiv:2405.16015 (2024).
- [Lor91] D. J. Lorenzini, A finite group attached to the Laplacian of a graph, *Discrete Math.* 91 (1991), 277–282.
- [LZ22] Y. Len, D. Zakharov, Kirchhoff's theorem for Prym varieties, with an appendix by S. Casalaina-Martin, *Forum Math. Sigma* 10 (2022), Paper No. e11; arXiv:2012.15235.
- [MGM19] J. Marx-Kuo, J. Gao, V. McDonald, The sandpile group of Cayley graphs, poster, Joint Mathematics Meetings, Baltimore, January 2019.
- [OEIS] The On-Line Encyclopedia of Integer Sequences, sequence A193134, accessed 5 October 2026.
- [RT14] V. Reiner, D. Tseng, Critical groups of covering, voltage and signed graphs, *Discrete Math.* 318 (2014), 10–40; arXiv:1301.2977.
- [Str28] R. Strassmann, Über den Wertevorrat von Potenzreihen im Gebiet der `p`-adischen Zahlen, *J. Reine Angew. Math.* 159 (1928), 13–28.
- [TW21] D. Tubbenhauer, P. Wedrich, Quivers for `SL_2` tilting modules, *Represent. Theory* 25 (2021), 440–480.
- [vSt40] K. G. C. von Staudt, Beweis eines Lehrsatzes, die Bernoullischen Zahlen betreffend, *J. Reine Angew. Math.* 21 (1840), 372–374.
- [VZ24] M. Vetluzhskikh, D. Zakharov, Critical groups in harmonic abelian quotients, arXiv:2409.04629 (2024).
- [Wil90] R. M. Wilson, A diagonal form for the incidence matrices of `t`-subsets vs. `k`-subsets, *European J. Combin.* 11 (1990), 609–615.
- [Yue24] C. H. Yuen, The critical groups of Adinkras up to 2-rank of Cayley graphs, *Electron. J. Combin.* 31 (2024), Paper No. P1.38; arXiv:2301.02517.
