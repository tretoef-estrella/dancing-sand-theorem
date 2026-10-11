# C36 — the podium: Lemma 9.7 and Corollary 1.6

Piece C36 of the Lean formalization of «The Dancing Sand Theorem» (paper v8, §9.2 Lemma 9.7 and the proof of Corollary 1.6; §1.4 Corollary 1.6). Folder `RequestProject/PodiumCor/`, namespace `PodiumCor`.

Corollary 1.6 gives the `n + 1` largest cyclic factors of `Syl_2 K(Q_n)`. In particular it proves Gao, Marx-Kuo, McDonald and Yuen's Theorems 4.1 and 4.2, their Conjecture 4.14, and the `(n+1)`-th factor conjectured on the 2019 poster of Marx-Kuo, Gao and McDonald. The exponents `c_r` of the cyclic factors are stated without choosing a decomposition, through the layers `|2^j S / 2^{j+1} S|` of the finite abelian 2-group `S` (this generalizes the two layers of C34).

## Setting (reused, not redefined)

- C3 (`Rulers`): `phi`, `v2`, `kappa`, `clock`, `oE`, `lam`.
- C13 (`Dance`): `mCount`. C14 (`Windows`): `Ids`.
- C16 (`FamilyGroup`): `yPool`, `yPool0`, `Q`.
- C17 (`CubeLaplacian`): `K`, `Syl2`.
- C31 (`FamDec`): `Vdot`, `L`, `m`, `L1`, `L2`, `L3`, `L4`, `M3`, `M4`.
- C32 (`Families`): `ds`, `ds_zero`, `ds_odd`, `ds_even`, `B0b`.
- C33 (`MainTheorem`): `XFam`, `M1`, `M2`, `S1_lam`, `S1_succ`, `S2_length`, `S3_subset`, `S3_card`, `S4`, `S4_Q0`.
- C34 (`BaiCounts`): `twoPow`, `l0`, `l1`, `l0_congr`, `l0_prod`, `l0_pi`, `l0_padic`, `l0_Q`, `A3_pos`, `A3_zero`.
- C35 (`Podium`): `P`, `tAt`, `Y`, `La`, `Lb`, `Lc_Y_eq_clear`, `Lc_Y_le_Y_one`, `Ld`, `Ld_one`.
- C35b (`PodiumWalk`): `H1`, `H2`, `C1`, `T1`, `T2`, `T3`, `Z1`, `Z2`.

Throughout: for `λ : ℕ`, `d = ds λ`, `k = d.length`, `I = Windows.Ids d`, `s = I.card` (`= Dance.mCount d`), `N = 2 ^ s`; `S n := CubeLaplacian.Syl2 (CubeLaplacian.K n)` as an additive group.

## Definitions

- **Layers.** For an additive commutative group `G` and `j : ℕ`,
  `layer G j := Nat.card (twoPow G j ⧸ (twoPow G (j + 1)).addSubgroupOf (twoPow G j))`.
  For `G = ⊕ ℤ/2^{e_i}` (`ℤ/2^∞ = ℤ_2`), `layer G j = 2 ^ #{i : j < e_i}`.
- **Exponents.** `cExp G r := sSup {e : ℕ | 1 ≤ e ∧ 2 ^ r ≤ layer G (e − 1)}` (`sSup` in `ℕ`; `0` if the set is empty). For `G = ⊕ ℤ/2^{e_i}` finite and `r ≥ 1`, `cExp G r` is the `r`-th largest `e_i` (`0` if there are fewer than `r`). The paper's `c_r(Q_n)` is `cExp (S n) r`.
- **The exponents read off the families** (a `Multiset ℕ`):
  - `smallExps λ := Σ_{a ∈ Finset.Ico 1 k} Multiset.replicate (2 ^ (s + k − 1 − a)) a`;
  - `bigExps λ 0 := (Finset.range (N − 1)).val.map (fun q => (FamilyGroup.yPool0 d q).toNat)`, and for `i ≥ 1`, `bigExps λ i := (Finset.range N).val.map (fun p => (FamilyGroup.yPool d i p).toNat)`;
  - `famExps λ i := smallExps λ + bigExps λ i`;
  - `exps n := ((FamDec.L n).map (fun λ => famExps λ ((n − λ) / 2))).sum`.
  (The extra `ℤ_2` of the family `λ = n` at shift `0` is left out: it cancels the `ℤ_2` on the left of C33 (M2).)
- **`g`.** `gmax N : ℤ` := `max_{1≤x<N} φ(x)` for `N ≥ 2` (any value for `N ≤ 1`). Encoding free; prove
  **(g0)** for `N ≥ 2`: `(∃ x, 1 ≤ x ∧ x < N ∧ gmax N = Rulers.phi x) ∧ ∀ x, 1 ≤ x → x < N → Rulers.phi x ≤ gmax N`.

## Part D — the layers

**(D0)** `layer G 0 = BaiCounts.l0 G` and `layer G 1 = BaiCounts.l1 G`.

**(D1)** `layer` is invariant under `≃+`; `layer (G × H) j = layer G j * layer H j`; for a `Fintype` index, `layer (Π i, G i) j = Π_i layer (G i) j`; `layer ℤ_[2] j = 2`; `layer (FamilyGroup.Q e) j = if j < e then 2 else 1` (`Q e = ℤ_[2] ⧸ Ideal.span {2 ^ e}`).

## Part E — the exponents of `Syl_2 K(Q_n)` (the dictionary)

For every `n ≥ 1`:

**(E1)** for every `j`: `layer (S n) j = 2 ^ ((exps n).countP (fun e => j < e))`.

**(E2)** for every `r ≥ 1` and `e ≥ 1`: `e ≤ cExp (S n) r ↔ r ≤ (exps n).countP (fun x => e ≤ x)`.

**(E3)** for every `r ≥ 1`: `cExp (S n) r = ((exps n).sort (fun a b => b ≤ a)).getD (r − 1) 0` (the `r`-th largest exponent).

*Sketch.* C33 (M2) and C33 (S4) write `ℤ_[2] × S n` as a product of the groups `Q a` (small clocks, with the factor `a = 0` trivial), `Q (yPool …).toNat`, `Q (yPool0 …).toNat` and one `ℤ_[2]` at the family `λ = n`; apply (D1) and cancel the two factors `ℤ_[2]` (`layer ℤ_[2] j = 2 ≠ 0`). (E2) follows from (E1): `2^r ≤ 2^c ⟺ r ≤ c`, and `countP (e ≤ ·)` is antitone in `e` and `0` for `e` large, so the set of (`cExp`) is a nonempty initial segment `[1, e_0]` or empty. (E3) from (E2).

## Part L — Lemma 9.7 (multiplicities)

**(L1)** `FamDec.m n n = 1` for `n ≥ 1`.

**(L2)** `FamDec.m (n − 2) n = n − 1 − (if n % 2 = 0 then 1 else 0)` for `n ≥ 2`.

**(L3)** for odd `n ≥ 5`: `FamDec.m (n − 4) n = (n − 1) * (n − 2) / 2 − 1 − (if n % 4 = 1 then 1 else 0)`, and this is `≥ 4`.

*Sketch.* The paper peels the weights `n − 2`, `n − 4` of `V^{⊗n}`. In Lean the recursion `L (n + 1) = (L n).flatMap Vdot` can be used directly: `m μ (n + 1) = Σ_{λ} m λ n · count μ (Vdot λ)`, and only `λ ∈ {n, n − 2, n − 4, …}` can reach `μ ≥ n − 3` (C33 (M3): families of `L n` lie in `[1, n]` with the parity of `n`). Check: `L 2 = [2]`, `L 3 = [1, 1, 3]`, `m 1 5 = 4`.

## Part W — the shift-2 clocks of an odd family

**(W1)** If `1 ≤ k`, `0 ∉ I` and `D ⊆ I`: `Rulers.clock k I 2 D = Rulers.clock k I 1 D`.

**(W2)** For odd `λ`: `FamilyGroup.yPool (ds λ) 2 = FamilyGroup.yPool (ds λ) 1`.

*Sketch.* `clock k I i D = φ(ξ_D) + κ(i + o_D − 1, ξ_D) + h(D)`. With `0 ∉ I` and `k ≥ 1`, `λ + 1 = 2^k + o_I` is even and `o_D` is even, so `ξ_D` is even, and `κ(o_D + 1, ξ_D) = κ(o_D, ξ_D)` (adding `1` to an even number sets bit 0 and creates no carry: `s_2(o_D + 1) = s_2(o_D) + 1`, `s_2(o_D + 1 + ξ_D) = s_2(o_D + ξ_D) + 1`). (W2): `λ` odd gives `0 ∉ I` and `k ≥ 1`; the pooled clocks are the fit of the same sequence.

## Part B — the bounds of the proof of Corollary 1.6

Put `G := gmax (n − 1)` (paper: `g(n − 1) = max_{1≤y≤n−2} φ(y)`). For `n ≥ 4`:

**(B0)** for `λ ≥ 1` with `FamDec.m λ n ≠ 0`: `((ds λ).length : ℤ) − 1 < G` (every small clock is below `G`).

**(B1)** for `λ ≥ 1` with `FamDec.m λ n ≠ 0` and `i := (n − λ) / 2 ≥ 2`: `yPool (ds λ) i p ≤ G` for every `p < N` (from C35b (C1): `y ≤ λ + i = n − i ≤ n − 2`).

**(B2)** with `d = ds (n − 2)`: `yPool d 1 0 = max G (φ (n − 1))`, and `yPool d 1 p ≤ G` for `1 ≤ p < N` (C35b (T1), (T2), C35 (Ld), `Y_1 ≤ n − 2`).

**(B3)** with `d = ds n`, `k`, `I`, `s ≥ 1`: `yPool0 d q ≤ G` for `1 ≤ q < N − 1` (C35b (Z2); `Y_l ≤ n − 2` for `l ≥ 2`), and `φ(Y_l) ≤ G` for `2 ≤ l ≤ s`.

**(B4)** `n` even: `φ(n) − 1 ≤ yPool0 (ds n) 0 ≤ max G (φ(n) − 1)`.

**(B5)** `n % 4 = 1`: `φ(n − 1) − 2 ≤ yPool0 (ds n) 0 ≤ max G (φ(n − 1) − 2)`.

**(B6)** `n % 4 = 3` and `1 ≤ (Windows.Ids (ds n)).card`: `yPool0 (ds n) 0 ≤ G`.

**(B7)** `n` even: `yPool (ds (n − 2)) 1 0 = G` and `yPool (ds (n − 2)) 1 1 = G` (and `N ≥ 2` for this family) — C35b (T1), (T3), with `φ(n − 1) = n − 1 ≤ φ(n − 2)`.

**(B8)** `n` odd: `yPool (ds (n − 4)) 2 0 = G` — (W2), C35b (T1), C35 (Ld): it is `g(n − 2)`, which is `G` because `φ(n − 2) = n − 2 ≤ φ(n − 3)`.

(B4)–(B6) come from C35b (Z1): `yPool0 (ds n) 0` is the maximum of `φ(Y_1) − 2^{t₁}` and of `φ(Y_l)`, `2 ≤ l ≤ s`, with `Y_1 = n + 1 − 2^{t₁}`; `t₁ = 0` for `n` even, `t₁ = 1` for `n ≡ 1 (mod 4)`, `t₁ ≥ 2` for `n ≡ 3 (mod 4)`.

## Part P — Corollary 1.6 (the podium)

Write `c r := cExp (S n) r` and `G := gmax (n − 1)`. For every `n ≥ 4`:

**(P1)** `n` even: `(c 1 : ℤ) = max G (φ n − 1)` and `(c r : ℤ) = G` for `2 ≤ r ≤ n + 1`.

**(P2)** `n` odd and `φ(n − 1) ≤ G`: `(c r : ℤ) = G` for `1 ≤ r ≤ n + 1`.

**(P3)** `n` odd and `φ(n − 1) > G`: `(c r : ℤ) = φ(n − 1)` for `1 ≤ r ≤ n − 1`, `(c n : ℤ) = max G (φ(n − 1) − 2)` and `(c (n + 1) : ℤ) = G`.

*Sketch (paper, proof of Corollary 1.6).* By (E2) it suffices to count the exponents `≥ e`. By (B0)–(B3), (B6) the exponents above `G` are at most the `m_{n−2}(n)` copies of `yPool (ds (n−2)) 1 0 = max(G, φ(n − 1))` and the single `yPool0 (ds n) 0`. Enough exponents equal `G`: for `n` even, the `n − 2` copies of the family `n − 2` give two each (B7) — `2(n − 2) ≥ n + 1` for `n ≥ 6`; for `n = 4`, `c 1 = φ(4) − 1 = 5 > G = 3` and `4` exponents at `G` suffice; for `n` odd, the `n − 1` copies of `yPool (ds (n−2)) 1 0 ≥ G` and the `m_{n−4}(n) ≥ 4` copies of (B8). Then read off with (B4), (B5) and (L2), (L3).

## Part G — the statements of Gao et al. and of the poster

**(G1)** [GMMY24, Theorems 4.1, 4.2] for `n ≥ 3`: `(c 1 : ℤ) = max (gmax n) (v2 n + n − 1)` and `(c r : ℤ) = gmax n` for `2 ≤ r ≤ n − 1`.

**(G2)** [GMMY24, Conjecture 4.14] for `n ≥ 3`: `(c n : ℤ) = max (gmax (n − 1)) (v2 (n − 1) + n − 3)`.

**(G3)** [MGM19] for `n ≥ 4`: `(c (n + 1) : ℤ) = gmax (n − 1)`.

*Sketch.* For `n ≥ 4` from (P1)–(P3): `gmax n = max G (φ(n − 1))`, `v2 n + n − 1 = φ(n) − 1`, `v2(n − 1) + n − 3 = φ(n − 1) − 2`; for `n` odd `φ(n) − 1 = n − 1 ≤ φ(n − 1)`; for `n` even `φ(n − 1) = n − 1 ≤ φ(n − 2) ≤ G` and `n − 3 < G`. For `n = 3`: `Syl_2 K(Q_3) ≅ ℤ/2 ⊕ (ℤ/8)^2`, i.e. `exps 3 = {1, 3, 3}` (families `L 3 = [1, 1, 3]`), so `c 1 = c 2 = 3`, `c 3 = 1`, and `gmax 3 = 3`, `gmax 2 = 1`.

## Notes

- Nothing is cited. Every step is a certified piece plus finite-group bookkeeping and counting.
- Brute force (`chkC36.py`, written from §1.2 and §9.2): (E) `exps n` against the 2-adic Smith form of the Laplacian of `Q_n`, `1 ≤ n ≤ 9`, and `cExp` from the layers against the `r`-th largest exponent, `n ≤ 60`; (L) `n ≤ 300`; (W) `k ≤ 8`; (B0)–(B8) `4 ≤ n ≤ 160`; (P1)–(P3), (G1)–(G3) `3 ≤ n ≤ 160`. Controls (each must fire): `c_n = G` always; (L2) without `[n even]`; (W) with `0 ∈ I`; the layer with `≤` for `<`; `c_1 = φ(n)` for even `n`.
- Encodings are free provided they are faithful; say in a docstring how each object is encoded. More general statements are welcome (say so). Say if a hypothesis is unused.
