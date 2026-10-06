# The theorems — a guided tour

This page walks through the results of [the paper](paper/THE_DANCING_SAND_THEOREM_v8.pdf) (version 8) in the order of the proof, says what each one does, and points to the statements a referee should read first. Section and statement numbers are those of version 8. The authoritative statements are the paper's; nothing here replaces them.

Notation: `K(Q_n)` is the sandpile group of the `n`-cube, `Syl_2` its `2`-part, `ℤ_2` the `2`-adic integers, `v_2` the `2`-adic valuation, `κ(a, b)` the number of carries in the binary addition `a + b`.

---

## The two main results

**Main Theorem (the Dancing Sand Theorem, §1.2; proof in §8).** For every `n ≥ 1`,
`Syl_2 K(Q_n) ⊕ ℤ_2 ≅ ⊕_λ X(λ, (n − λ)/2)^{m_λ(n)}`, the sum over `1 ≤ λ ≤ n` with `λ ≡ n (mod 2)`.
- `m_λ(n)` is the multiplicity of the indecomposable tilting module `T(λ)` of `SL_2` in characteristic `2` in `V^{⊗n}`; it is given by a recursion of three lines.
- `X(λ, i)` is made of **small clocks**, `⊕_{a=1}^{k−1} (ℤ/2^a)^{2^{|I|+k−1−a}}`, and `2^{|I|}` **big clocks** `ℤ/2^{ŷ_i(D)}`, one for each subset `D` of `I` (a **dancer**), where `λ + 1 = 2^k + Σ_{t∈I} 2^t`.
- The big clocks are the integer antitonic fit (pool-adjacent-violators) of explicit **raw clocks** `u_i(D) = φ(ξ_D) + κ(i + o_D − 1, ξ_D) + h(D)`, with `ξ_D = λ + 1 − 2o_D`, `o_D = Σ_{t∈D} 2^t` and `φ(x) = x + v_2(x)`. In the cube every block mean is an integer (Lemma 7.9), so the rounding never acts.

**Theorem DW (the fold law, §1.3; proof in §10).** For every `n ≥ 1`, `Syl_2 K(Q_n/⟨𝟙⟩) ≅ 2·Syl_2 K(Q_n)`. Equivalently, the cube's group is the folded cube's with every exponent raised by one, plus `a_n = 2^{n−2} − 2^{⌊(n−2)/2⌋}` factors `ℤ/2`.

«Dry» is reduction modulo `2`; «wet» is the lattice over `ℤ_2`. Modulo `2` a doubled family `T(2l + 1)` becomes a Frobenius twist; over `ℤ_2` the twist has an integral form on which every power of `2` survives. The fold dries the cube by exactly one layer (§1.7).

---

## The proof, step by step

### 1. The group ring as an `SL_2`-module (§2)
In `ℤ[(ℤ/2)^n]` the Laplacian is multiplication by `σ = Σ_i (1 − x_i)`. In the basis `s_S = ∏_{i∈S}(1 − x_i)` it is `U + 2D` (`U` the raising operator of the Boolean lattice, `D` the rank). Identifying `s_S` with pure tensors of `V^{⊗n}` gives **`σ = F + n − H`**, an element of the Kostant `ℤ`-form of `U(sl_2)` (**Lemma 2.2, the dictionary**). **Corollary 2.3**: `ℤ_2 ⊕ Syl_2 K(Q_n)` is the cokernel of `F + n − H` over `ℤ_2`, summand by summand of any decomposition of `V^{⊗n}`.

### 2. The family decomposition (§3)
- **Proposition 3.1** and **Lemma 3.2 (Lemma W)**: the doubling functor `Φ`, an integral replacement for the Frobenius twist, and an elementary lifting lemma for `SL_2` over `ℤ_2`.
- **Theorem 3.6**: `V^{⊗n} ⊗ ℤ_2 ≅ ⊕_λ T(λ)^{m_λ(n)}` as lattices over the hyperalgebra, with `T(2l + 1) = Φ(T(l))` and `T(2l + 2) = V ⊗ Φ(T(l))`.
- **Theorem 3.8**: since `σ` is carried by every isomorphism, the group splits family by family.

The decomposition is proved here; it is not cited from the general theory of tilting modules (Remark (2) after Theorem 3.6: it uses Lemma 3.2, Weyl's theorem on complete reducibility over `ℚ`, and the completeness of `ℤ_2`).

### 3. The dance: Theorem D (§4)
- **Proposition 4.1 (the twist move)** and **Proposition 4.2 (the split move)**: one step of block Gaussian elimination each, eliminating unit pivots and halving a Schur complement. The split move separates the two basis vectors of `V`, so every dancer becomes two.
- **Proposition 4.3**: after the `k` moves of the binary digits of `λ + 1`, the family's group is the small clocks plus `coker(2^k M)`, with `M` a lower triangular matrix of size `2^{|I|}` indexed by the dancers.
- **Theorem 4.4 (windows)** gives `M` in closed form: products of payments over windows of floors, times the coefficients of an explicit polynomial. **Lemma 4.5 (the deficit law)** gives the valuations of those coefficients.
- **Theorem D** collects it: `v_2(M_{DD'}) = 1 − K + o(D∖D') + δ(D∖D') + Σ_{d=o_D}^{o_{D'}+K−1} (α + v_2(i + d))`.

### 4. The valuations (§5)
- **Proposition 5.2 (the cost form)** writes the valuation of every entry as a row term («ruler»), a column term and a remainder `γ` («gold») that vanishes exactly on the «golden» arrows.
- **Propositions 5.3 and 5.4** identify the resulting clocks with the raw clocks of §1.2, for `i ≥ 1` and for `i = 0`.

### 5. The ceiling: Theorem O (§6)
- **Lemma 6.1**: the `r`-th determinantal divisor of `M` is bounded below by the cheapest `r`-matching in its support (a tropical bound).
- **Theorem 6.2 (Theorem O)**: for every `r` there is **exactly one** bijection between the last `r` rows and the first `r` columns all of whose arrows are golden. Its proof is an induction on the top binary digit.
- **Corollary 6.3**: the natural minor therefore has a unique term of least valuation, which is a partial sum of the raw clocks.
- **Lemma 6.4 (convexity)** turns it into the partial sum of the pooled clocks.
- **Theorem 6.5**: if the floor meets the ceiling, the Smith exponents are the pooled clocks.

### 6. The floor: Theorems U and F (§7)
- **Theorem 7.4 (Theorem U)** reduces the lower bound to finding a «potential»: row and column functions, non-increasing, whose differences equal the pooled clocks and never exceed the cost of an arrow.
- **Theorem 7.8 (Theorem F)** builds that potential for every «house» `(I, k, ℓ, α)`, digit by digit from the bottom of `λ + 1`. It is the longest combinatorial argument of the paper.
- **Lemma 7.2 (cuts and shifts)** and **Lemma 7.9 (integrality)** handle the pooling.
- **Theorem 7.10**: the Smith form of `M` is the pooled sequence of clocks, for every family and every shift.

**§8** assembles the Main Theorem from Theorems 3.8, D and 7.10.

### 7. The consequences (§9)
- **Corollary 1.5**: Bai's two counts.
- **Corollary 1.6 (the podium)**: the `n + 1` largest cyclic factors. It re-proves Gao et al.'s Theorems 4.1–4.2, and proves their Conjecture 4.14 and the `(n+1)`-th factor stated on the 2019 poster.
- **Corollary 1.7 / Theorem 9.10 (the mirror that doubles)**: Gao et al.'s Conjecture 5.4. Each dancer of the cube of dimension `2^e − 1` becomes two dancers with the same raw clock in dimension `2^e`.

### 8. The fold law (§10)
- **Lemma 10.1**: on every family the antipode acts as `±exp(F)`.
- **Lemmas 10.4 and 10.5**: the folded group of an odd family is the cokernel of an operator that differs from the doubled one by a perturbation `Σ ζ_m F^{(m)}` by higher divided powers; an even family is two odd ones glued.
- **Theorem 10.12 (rigidity)**: if the dance of the perturbed operator is «clean», its final matrix differs from the unperturbed one by a factor `1 + E'` with `v_2(E') ≥ 1`. So the support, the entry valuations and the Smith form are the same.
- **Theorem 10.15 (cleanliness)**: the dance is clean. The coefficients of every level lie in a ring `𝒦` of `2`-adic functions of twice the position, on which a shift-invariant reduction makes every Schur complement vanish modulo `2`. Lemma 10.13 uses Strassmann's theorem.
- **Theorem 10.16** and **Corollary 10.17** give the fold law on the odd families.
- **Lemmas 10.18–10.20** (modulo 2, the glue, the bend) and **Theorem 10.22** give it on the even families.

**§10.8** assembles Theorem DW and Corollary 1.4, the whole sandpile group of the folded cube.

---

## What is measured, not proved

- **The turned lid** (§11, question 2): for `a + b = n ≤ 12`, `Syl_2 K(Q_a □ C_b) ≅ Syl_2 K(Q_b □ C_a)`, with `C_b` the folded `b`-cube, although the graphs are not isomorphic. Theorem DW is its degenerate end. We have no proof.
- **Remark (2) of §10.5**: experiments on the hypotheses of Theorem 10.15. With random constant weights on the higher divided powers, some dances are not clean when the payments, or the coefficient of `F`, are also random; with the coefficients of the cube, all 496 dances measured are clean.

## Open questions (§11)

1. Other quotients of the cube by binary codes.
2. The turned lid.
3. A direct proof of the fold law through the signed graph of Reiner and Tseng.
4. A module-theoretic meaning of the pooling.
5. Other primes and the Hamming graphs.
6. Formal verification, which we have planned ([README](README.md#formal-verification-planned)).

---

[README](README.md) · [Where to attack](WHERE_TO_ATTACK.md) · [How to verify](HOW_TO_VERIFY.md)
