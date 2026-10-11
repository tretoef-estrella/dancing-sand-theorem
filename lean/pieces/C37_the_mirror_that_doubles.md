# C37 — the mirror that doubles: Lemmas 9.8–9.9, Theorem 9.10 and Corollary 1.7

Piece C37 of the Lean formalization of «The Dancing Sand Theorem» (paper v8, §9.3; §1.4 Corollary 1.7). Folder `RequestProject/Mirror/`, namespace `Mirror`.

Corollary 1.7 is Gao, Marx-Kuo, McDonald and Yuen's Conjecture 5.4: for every `e ≥ 1`,
`Syl_2 K(Q_{2^e}) ≅ Syl_2 K(Q_{2^e − 1})^2 ⊕ ℤ/2^{2^e + e − 1}`.
Each family `λ` of the cube `N = 2^e − 1` becomes the family `λ + 1` of the cube `n = 2^e`, with the same multiplicity and shift, and each of its dancers becomes two dancers with the same raw clock.

## Setting (reused, not redefined)

- C1 (`AntitonicFit`): `fit`, `ifit`, `toR`, `levelSet`, and the lemmas about them.
- C3 (`Rulers`): `phi`, `v2`, `s2`, `kappa`, `oE`, `minOr`, `next`, `h`, `t1`, `hSum`, `lam`, `xi`, `clock`.
- C7 (`TheoremF`): `dancer`. C13 (`Dance`): `mCount`. C14 (`Windows`): `Ids`, `card_Ids`.
- C16 (`FamilyGroup`): `SC`, `Q`, `yPool`, `yPool0`.
- C17 (`CubeLaplacian`): `K`, `Syl2`.
- C31 (`FamDec`): `Vdot`, `Vdot_odd`, `L`, `L_succ`, `m`, `M3`, `M4`.
- C32 (`Families`): `ds`, `ds_zero`, `ds_odd`, `ds_even`, `B0b`.
- C33 (`MainTheorem`): `XFam`, `M2equiv`, `M2`, `S1_lam`, `S1_succ`, `S1_xi`, `S3_subset`, `S3_card`, `S4equiv`.
- C36 (`PodiumCor`): `smallExps`, `bigExps`, `famExps`, `exps`, `E1`.

Throughout: `S n := CubeLaplacian.Syl2 (CubeLaplacian.K n)` as an additive group; for `λ : ℕ`, `d = ds λ`, `k = d.length`, `I = Windows.Ids d`. For `e ≥ 1`: `N := 2^e − 1`, `n := 2^e`.

## Part A — Lemma 9.8 (the families of `N' + 1`, `N'` odd)

**(A1)** For odd `N'`: every element of `FamDec.L N'` is odd, and `FamDec.L (N' + 1) = (FamDec.L N').map (· + 1)`. Hence `FamDec.m (μ + 1) (N' + 1) = FamDec.m μ N'` for every `μ`, and `FamDec.m 0 (N' + 1) = 0`.

**(A2)** For odd `λ`: `(ds (λ + 1)).length = (ds λ).length`, `0 ∉ Windows.Ids (ds λ)`, `Windows.Ids (ds (λ + 1)) = insert 0 (Windows.Ids (ds λ))`, and `Dance.mCount (ds (λ + 1)) = Dance.mCount (ds λ) + 1`.

**(A3)** For every finite set `I` with `0 ∉ I` and every `q`: `TheoremF.dancer (insert 0 I) (2 * q) = TheoremF.dancer I q` and `TheoremF.dancer (insert 0 I) (2 * q + 1) = insert 0 (TheoremF.dancer I q)` (the dancers `D` and `D ∪ {0}` are adjacent in o-order).

**(A4)** For odd `λ`: `PodiumCor.smallExps (λ + 1) = PodiumCor.smallExps λ + PodiumCor.smallExps λ` (the small clocks are taken twice).

**(A5)** If `I ⊆ Finset.range k` and `0 ∉ I`: `Rulers.h k (insert 0 I) t = Rulers.h k I t` for every `t ∈ I`, `Rulers.h k (insert 0 I) 0 = Rulers.t1 k I`; hence for `D ⊆ I`: `Rulers.hSum k (insert 0 I) D = Rulers.hSum k I D` and `Rulers.hSum k (insert 0 I) (insert 0 D) = Rulers.hSum k I D + Rulers.t1 k I`.

*Sketch.* (A1) from C31 (M3) (the families of `L N'` have the parity of `N'`) and `Vdot (2l + 1) = [2l + 2]`, by `L_succ`. (A2) from `ds (2l + 1) = false :: ds l` and `ds (2l + 2) = true :: ds l`: the digit lists differ only at position `0`. (A3) The rank of `t ∈ I` in `insert 0 I` is its rank in `I` plus one, and `0` has rank `0`; the binary digits of `2q` and `2q + 1` above position `0` are those of `q`. (A4) By (A2), `2 ^ (s + 1 + k − 1 − a) = 2 ^ (s + k − 1 − a) + 2 ^ (s + k − 1 − a)`. (A5) `next` changes only at `0`.

## Part B — Lemma 9.9 (the raw clocks of the two cubes)

Let `k : ℕ`, `I ⊆ Finset.range k`, `D ⊆ I`, `i : ℕ`, `J := i + Rulers.oE D`, and `e : ℕ`.

**(B1)** (the cube `N`) If `2 ^ k + Rulers.oE I + 2 * i = 2 ^ e` and `1 ≤ J`:
`Rulers.clock k I i D = 2 ^ e − 2 * J + Rulers.v2 J + Rulers.s2 J + Rulers.hSum k I D` (in `ℤ`).

**(B2)** (the cube `n`) If `2 ^ k + Rulers.oE I + 2 * i = 2 ^ e + 1` and `1 ≤ J`:
`Rulers.clock k I i D = 2 ^ e + 1 − 2 * J + Rulers.s2 (J − 1) + Rulers.hSum k I D` (in `ℤ`).

*Sketch (paper).* In the cube `N`, `ξ = λ + 1 − 2 o_D = 2^e − 2J` and `J ≤ 2^{e−1} − 1` (since `J ≤ i + o_I` and `o_I < 2^k`), so `φ(ξ) = 2^e − 2J + 1 + v_2(J)`. With `a = J − 1`, `a + ξ = (2^e − 1) − J` and `ξ/2 = (2^{e−1} − 1) − a`, so `s_2(a + ξ) = e − s_2(J)`, `s_2(ξ) = e − 1 − s_2(a)`, and `κ(a, ξ) = s_2(J) − 1`. In the cube `n`, `ξ' = 2^e + 1 − 2J'` is odd and `J' ≤ 2^{e−1}`; with `a = J' − 1`, `a + ξ' = (2^e − 1) − a` and `ξ' = (2^e − 1) − 2a`, so `κ(a, ξ') = s_2(a)`. (`s_2((2^f − 1) − b) = f − s_2(b)` for `b < 2^f`.)

## Part C — Theorem 9.10 (the mirror that doubles)

**(C1)** Let `e ≥ 1`, `λ` odd with `λ < 2 ^ e − 1`, `i := (2 ^ e − 1 − λ) / 2`, `k := (ds λ).length`, `I := Windows.Ids (ds λ)`, `I' := Windows.Ids (ds (λ + 1))`, `k' := (ds (λ + 1)).length`. For every `D ⊆ I`:
`Rulers.clock k' I' i D = Rulers.clock k I i D` and `Rulers.clock k' I' i (insert 0 D) = Rulers.clock k I i D`.

(Here `i ≥ 1`, and `(2 ^ e − (λ + 1)) / 2 = i` is the shift of the family `λ + 1` in the cube `2^e`.)

*Sketch (paper).* For `D' = D`: `J' = J`, `h'(D) = h(D)` (A5), and `s_2(J − 1) = s_2(J) − 1 + v_2(J)`, so Lemma 9.9 gives the same value. For `D' = D ∪ {0}`: `J' = J + 1` and `h'(D ∪ {0}) = h(D) + t_1` (A5), so the clock is `u_N(D) + t_1 − 1 − v_2(J)`. Finally `2i = 2^e − 2^k − o_I` with `k < e`, so `v_2(i) = t_1 − 1`; every digit of `D` is `≥ t_1`, so `v_2(J) = v_2(i + o_D) = t_1 − 1`.

## Part F — the fit of a doubled sequence

**(F1)** For every `N`, `x : ℕ → ℝ` and `j < 2 * N`: `AntitonicFit.fit (2 * N) (fun j => x (j / 2)) j = AntitonicFit.fit N x (j / 2)`.

**(F2)** For every `N`, `x : ℕ → ℤ` and every `j`: `AntitonicFit.ifit (2 * N) (fun j => x (j / 2)) j = AntitonicFit.ifit N x (j / 2)`.

*Sketch.* (F1) by the characterization of the fit (C1, Lemma 7.1 and its uniqueness): the doubled fit is antitonic and its level sets are the doubled level sets, on which the doubled sequence has the doubled means. (F2) A doubled level set, with `2P` positions and sum `2S`, gives the first `2(S mod P)` positions `⌈S/P⌉` and the rest `⌊S/P⌋`; the rank of `j` is twice the rank of `j / 2` plus `j % 2`, and `rank < 2(S mod P) ⟺ rank / 2 < S mod P`.

## Part X — Corollary 1.7 for the exponents

Let `e ≥ 1`, `λ` odd with `λ < 2 ^ e − 1` and `i := (2 ^ e − 1 − λ) / 2`.

**(X1)** `FamilyGroup.yPool (ds (λ + 1)) i j = FamilyGroup.yPool (ds λ) i (j / 2)` for every `j`.

**(X2)** `PodiumCor.bigExps (λ + 1) i = PodiumCor.bigExps λ i + PodiumCor.bigExps λ i`.

**(X3)** `PodiumCor.famExps (λ + 1) i = PodiumCor.famExps λ i + PodiumCor.famExps λ i`.

**(X4)** (the top family) `PodiumCor.famExps (2 ^ e) 0 = PodiumCor.famExps (2 ^ e − 1) 0 + PodiumCor.famExps (2 ^ e − 1) 0 + {2 ^ e + e − 1}`.

**(X5)** (Corollary 1.7, exponent form) `PodiumCor.exps (2 ^ e) = PodiumCor.exps (2 ^ e − 1) + PodiumCor.exps (2 ^ e − 1) + {2 ^ e + e − 1}`.

*Sketch.* (X1) from (A2), (A3), (C1) and (F2): the raw sequence of `(λ + 1, i)` in o-order is that of `(λ, i)` with every entry written twice. (X2) from (X1) (`2^{s+1}` positions). (X3) from (A4) and (X2). (X4) The family `2^e − 1` has `k = e` and `I = ∅`, so `bigExps (2^e − 1) 0 = 0`; the family `2^e` has `k = e`, `I = {0}`, its small clocks twice (A4), and the one big clock at shift `0`, `yPool0 (ds (2^e)) 0 = Rulers.clock e {0} 0 {0} = 2^e + e − 1` (`ξ = 2^e − 1`, `κ = 0`, `h_0 = e`). (X5) by (A1) the families of `2^e` are the `λ + 1`, `λ ∈ L (2^e − 1)`, with the same shift `(2^e − (λ+1))/2 = (2^e − 1 − λ)/2`; the family `2^e − 1` gives (X4), and every other family is odd and `< 2^e − 1`, so (X3) applies.

## Part Y — Corollary 1.7 (group form)

For every `e ≥ 1`:

**(Y1)** `Nonempty (ℤ_[2] × S (2 ^ e) ≃+ ℤ_[2] × ((S (2 ^ e − 1) × S (2 ^ e − 1)) × FamilyGroup.Q (2 ^ e + e − 1)))`.

**(Y2)** `Nonempty (S (2 ^ e) ≃+ (S (2 ^ e − 1) × S (2 ^ e − 1)) × ZMod (2 ^ (2 ^ e + e − 1)))`.

*Sketch.* By C33 (M2) both sides are products over the families. For odd `λ < 2^e − 1` and `i ≥ 1`: `XFam (λ + 1) i ≃+ XFam λ i × XFam λ i` (C33 (S4) for the small clocks with (A2); (X1) for the big clocks: `Fin (2 · M) → A ≃ (Fin M → A) × (Fin M → A)`). The family `2^e − 1` is `SC (ds (2^e−1)) × (ℤ_[2] × Π_{Fin 0} …)` and the family `2^e` is `SC (ds (2^e)) × (ℤ_[2] × Q (2^e + e − 1))`, with `SC (ds (2^e)) ≃+ SC (ds (2^e − 1))²`. To cancel `ℤ_[2]`, pass to torsion subgroups (`AddCommGroup.torsion`): an additive equivalence maps torsion onto torsion, `ℤ_[2]` is torsion-free, and `S n`, `Q e` and `SC` are torsion (finite, or killed by a power of `2`). `FamilyGroup.Q a ≃+ ZMod (2 ^ a)` through `PadicInt.toZModPow` (its kernel is `span {2 ^ a}`). (Y1) follows from (Y2).

## Checks

- Brute force (`chkC37.py`, written from §1.2 and §9.3; family machinery copied from `chkC36.py`): (A1) odd `N' ≤ 129` (multiplicities); (A2)–(A5) odd `λ < 600`; (B1), (B2) every family with `k ≤ 9`, every `D`, `e ≤ 10`; (C1) every odd `λ < 2^e − 1`, `e ≤ 10`; (F2) 3000 random sequences; (X1)–(X5) `e ≤ 8` (`n = 256`); and the exponents of `Syl_2 K(Q_n)` from the 2-adic Smith form of the Laplacian of `Q_n` for `n = 2, 4, 8`, against `exps n` and against `2 · exps (n − 1) + {2^e + e − 1}` (for `n = 8`: `{1⁵⁶, 2², 4¹⁶, 5¹², 6²⁸, 7¹², 10¹}`). 83 102 checks, 0 failures.
- Controls (each fires): (X5) without the extra factor; with `2^e + e` instead; (C1) `D ∪ {0}` at shift `i + 1`; (A1) for even `N'`; (F2) with concatenation `x ++ x` instead of doubling; (B1) without `v_2(J)`.
