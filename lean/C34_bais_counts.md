# C34 — Bai's two counts (Lemma 9.1 and Corollary 1.5)

Piece C34 of the Lean formalization of «The Dancing Sand Theorem» (paper v8, §9.1 Lemma 9.1, §1.4 Corollary 1.5 and its proof in §9.1). Folder `RequestProject/BaiCounts/`, namespace `BaiCounts`.

Corollary 1.5 re-proves Bai's two theorems (Bai 2003, Theorems 1.1 and 1.3): `Syl_2 K(Q_n)` has exactly `2^{n−1} − 1` cyclic factors, and exactly `a_n = 2^{n−2} − 2^{⌊(n−2)/2⌋}` of them are `ℤ/2` (`n ≥ 2`). The numbers of cyclic factors are stated without choosing a decomposition, by the two invariants `|S/2S|` and `|2S/4S|` of a finite abelian 2-group `S`.

## Setting (reused, not redefined)

- C3 (`Rulers`): `clock`, `xi`, `oE`, `hSum`, `phi`, `kappa`, `lam`.
- C7 (`TheoremF`): `dancer`, `lemma_0a`.
- C1 (`AntitonicFit`): `ifit`.
- C13 (`Dance`): `mCount`, `Idx`.
- C14 (`Windows`): `Ids`.
- C16 (`FamilyGroup`): `SC`, `Q`, `yPool`, `yPool0`.
- C17 (`CubeLaplacian`): `K`, `Syl2`.
- C31 (`FamDec`): `L`, `m`, `Vdot`, `M3`, `M4`, `L1`, `L2`, `L3`, `L4`.
- C32 (`Families`): `ds`, `ds_zero`, `ds_odd`, `ds_even`, `B0b`.
- C33 (`MainTheorem`): `XFam`, `M1`, `M2`, `S1_lam`, `S2`, `S2_length`, `S3_subset`, `S3_card`, `S4`, `S4_Q0`.

For an additive commutative group `G` and `j : ℕ` write `2^j G := {2^j • x | x ∈ G}`, an `AddSubgroup G`. The **layers** of `G` are
  `ℓ_0(G) := Nat.card (G ⧸ 2G)`  and  `ℓ_1(G) := Nat.card (2G ⧸ (4G as a subgroup of 2G))`.
For `G = ⊕_j ℤ/2^{e_j}` (with `ℤ/2^∞ = ℤ_2`) and every `e_j ≥ 1`, `log_2 ℓ_0` is the number of factors and `log_2 ℓ_1` the number of factors with `e_j ≥ 2`; so `log_2 ℓ_0 − log_2 ℓ_1` is the number of factors `ℤ/2`.

## Part A — Lemma 9.1 (clocks are at least 2)

**(A1)** For `k ≥ 1`, `I ⊆ Finset.range k`, `D ⊆ I` and `i : ℕ` with `1 ≤ i ∨ D ≠ ∅`: `2 ≤ Rulers.clock k I i D`.

*Sketch.* `ξ_D = 2^k + o_I − 1 + 1 − 2 o_D = 2^k + o_{I∖D} − o_D ≥ 1` (as `o_D ≤ o_I < 2^k`), `φ(ξ) ≥ ξ`, `κ ≥ 0` (carries), `h ≥ 0`. If `ξ_D = 1` then `o_{I∖D} = 0` and `o_D = 2^k − 1`, so `D = I = [0, k)` and `h(D) = Σ_{t<k} (next(t) − t) = k ≥ 1`. (When `D = ∅` and `i ≥ 1`, `ξ = λ + 1 = 2^k + o_I ≥ 2`.)

**(A2)** (pooled clocks) If every entry of `x : ℕ → ℤ` on `[0, N)` is `≥ c`, then `AntitonicFit.ifit N x j ≥ c` for every `j < N`. (A level set of entries `≥ c` has sum `S ≥ pc`, and the integer fit takes the values `⌈S/p⌉`, `⌊S/p⌋ ≥ c`.)

**(A3)** For `λ ≥ 1`: `2 ≤ FamilyGroup.yPool (ds λ) i p` for `i ≥ 1`, `p < N λ`; and `2 ≤ FamilyGroup.yPool0 (ds λ) q` for `q < N λ − 1`. (By (A1), (A2), C33 (S1)–(S3), and `dancer (I λ) (j + 1) ≠ ∅` for `j + 1 < N λ`.)

## Part F — the layers of one family

**(F1)** For `λ ≥ 1` and every `i`: `ℓ_0 (XFam λ i) = 2 ^ (2 ^ (mCount (ds λ) + (ds λ).length − 1))`.

**(F2)** For `λ ≥ 1` and every `i`: `ℓ_1 (XFam λ i) = 2 ^ (2 ^ (mCount (ds λ) + (ds λ).length − 1) − c₁(λ))`, where `c₁(λ) := 2 ^ (mCount (ds λ) + (ds λ).length − 2)` if `(ds λ).length ≥ 2` and `0` otherwise (the small clocks with `a = 1`).

*Sketch.* `ℓ_0`, `ℓ_1` are multiplicative over finite products and products of two (`(G × H)/2 = G/2 × H/2`). `ℓ_0(ℤ/2^e) = 2` for `e ≥ 1` (and `= 1` for `e = 0`), `ℓ_1(ℤ/2^e) = 2` for `e ≥ 2`, `= 1` for `e ≤ 1`; `ℓ_0(ℤ_2) = ℓ_1(ℤ_2) = 2`. By C33 (S4) the small clocks are `2^{|I|+k−1−a}` copies of `ℤ/2^a` for `a < k` (the factor `a = 0` is zero), and `Σ_{a=1}^{k−1} 2^{|I|+k−1−a} + 2^{|I|} = 2^{|I|+k−1}`. The big clocks have exponents `≥ 2` (A3); at shift 0 the extra `ℤ_2` and the `N − 1` pooled clocks make `N` factors.

## Part S — the counts of the families

**(S1)** For every `λ`: `Fintype.card (Dance.Idx (ds λ)) = 2 ^ ((ds λ).length + mCount (ds λ))` (= `dim T(λ)`).

**(S2)** For every `n`: `Σ_{j : Fin (L n).length} 2 ^ ((ds λ_j).length + mCount (ds λ_j)) = 2 ^ n`, `λ_j = (L n).get j`. (Either by induction on `n` with the rule `Vdot`, `Σ_{μ ∈ Vdot λ} 2^{k(μ)+|I(μ)|} = 2 · 2^{k(λ)+|I(λ)|}`, or from C31 (D2) and C32 (B1) by ranks.)

**(S3)** For every `n ≥ 1`: `Σ_{j} c₁(λ_j) · 4 + 2 · m 1 n + 4 · m 2 n = 2 ^ n`, and the families with `(ds λ).length ≤ 1` and `λ ≥ 1` are exactly `λ = 1` and `λ = 2`.

## Part B — Corollary 1.5 (Bai's two counts)

With `S n := CubeLaplacian.Syl2 (CubeLaplacian.K n)` (as an additive group):

**(B1)** For every `n ≥ 1`: `ℓ_0 (S n) = 2 ^ (2 ^ (n − 1) − 1)` — `Syl_2 K(Q_n)` has exactly `2^{n−1} − 1` cyclic factors.

**(B2)** For every `n ≥ 2`: `ℓ_1 (S n) = 2 ^ (2 ^ (n − 1) − 1 − a n)` with `a n := 2 ^ (n − 2) − 2 ^ ((n − 2) / 2)` — exactly `a_n` of the cyclic factors are `ℤ/2`.

*Sketch.* By C33 (M2), `ℤ_2 × S n ≃+ Π_j XFam λ_j i_j`; `ℓ_0`, `ℓ_1` are invariant under `≃+` and multiplicative; `ℓ_0(ℤ_2) = ℓ_1(ℤ_2) = 2`; so `2 · ℓ_0(S n) = Π_j 2^{2^{|I_j|+k_j−1}} = 2^{2^{n−1}}` by (F1), (S2); and `2 · ℓ_1(S n) = 2^{2^{n−1} − Σ_j c₁(λ_j)}` by (F2), with `Σ_j c₁(λ_j) = (2^n − 2 m_1(n) − 4 m_2(n))/4 = a_n` by (S3) and C31 (L3), (L4) (`m_1(n) = 2^{(n−1)/2}` for odd `n`, `m_2(n) = 2^{(n−2)/2}` for even `n`, and `m_1(n) = 0` for even `n`, `m_2(n) = 0` for odd `n` by C31 (M3)).

## Notes

- Nothing is cited. Every step is a certified piece plus finite-group bookkeeping.
- Brute force (`chkC34.py`): `ℓ_0`, `ℓ_1` of `Syl_2 K(Q_n)` from the 2-adic Smith form of the Laplacian of `Q_n` against (B1), (B2), `1 ≤ n ≤ 9` (and `n = 2, 3` by hand: `K(Q_2) = ℤ/4`, `Syl_2 K(Q_3) = ℤ/2 ⊕ (ℤ/8)^2`); (A1) on every `k ≤ 7`, `I ⊆ [0,k)`, `D ⊆ I`, `i ≤ 12`; (A2) on random sequences; (A3), (F1), (F2) on `λ ≤ 200`, `i ≤ 12`; (S1)–(S3) and (B1), (B2) from the families for `n ≤ 40`. Controls: `a n` with `2^((n−1)/2)`; clocks `≥ 3` (fails at `λ = 1`); `ℓ_0(ℤ_2) = 1`; the factor `a = 0` of the small clocks counted.
