# C51 — Theorem DW, the fold law, and its consequences (paper v8 §1.3, §10.8)

*Lean piece C51 of the Dancing Sand Theorem. Grepy Escribano, 10 October 2026. Folder `RequestProject/FoldLaw/`, namespace `FoldLaw`. Do not change any earlier file.*

Paper v8, **Theorem DW**: for every `n ≥ 1`, **`Syl_2 K̄(n) ≅ 2·Syl_2 K(Q_n)`**, where `K̄(n)` is the sandpile group of the folded cube `Q_n/⟨𝟙⟩`. Equivalently, `Syl_2 K(Q_n) ≅ (ℤ/2)^{a_n} ⊕ H`, where `H` has no factor `ℤ/2` and `2H ≅ Syl_2 K̄(n)`, with `a_n = 2^{n−2} − 2^{⌊(n−2)/2⌋}`. Also in §10.8: the number of cyclic factors of `Syl_2 K̄(n)` is `2^{n−1} − 1 − a_n`, and the `𝔽_2`-rank of the Laplacian of the folded cube is `a_n` (this is [GMMY24, Proposition 2.12]; Theorem DW explains their Remark 2.13).

**Everything is already in Lean except the assembly.**
- C38b `FoldGroup.P2` (Proposition 10.3): the fold law family by family implies Theorem DW.
- The fold law family by family:
  - odd families `λ = 2l + 1`: C49c `ZeroSmith.C5 l i`;
  - even families `λ = 2l + 2`: C50h `EvenZero.TT l i`.
- Bai's counts: C34 `BaiCounts.B1`, `BaiCounts.B2`, with the layers `BaiCounts.l0`, `BaiCounts.l1` and `BaiCounts.aN`.

## Setting (reuse; do not redefine)

- C17 `CubeLaplacian.G`, `CubeLaplacian.lap`, `CubeLaplacian.L`, `CubeLaplacian.coker`, `CubeLaplacian.K`, `CubeLaplacian.Syl2`.
- C38 `Fold.aElt`, `Fold.Gbar`, `Fold.lapBar`, `Fold.cokerBar`, `Fold.KBar`.
- C32 `Families.ds`; C16 `FamilyGroup.X`.
- C38b `FoldGroup.XbarFam`, `FoldGroup.twoM`, `FoldGroup.mem_twoM`, `FoldGroup.twoMCongr`, `FoldGroup.P2`, `FoldGroup.K2`, `FoldGroup.KBar_finite`, `FoldGroup.cokerBarEquivKBar`.
- C34 `BaiCounts.twoPow`, `BaiCounts.l0`, `BaiCounts.l1`, `BaiCounts.l0_congr`, `BaiCounts.l1_congr`, `BaiCounts.l0_pi`, `BaiCounts.l1_pi`, `BaiCounts.aN`, `BaiCounts.B1`, `BaiCounts.B2`.
- C49c `ZeroSmith.C5`; C50h `EvenZero.TT`.

No new definition is needed.

## Part H — the fold law on every family

- **(H)** For every `lam ≥ 1` and every `i`:
  `Nonempty (FoldGroup.XbarFam lam i ≃+ FoldGroup.twoM (FamilyGroup.X (Families.ds lam) 1 i))`.

## Part D — Theorem DW

- **(DW)** For every `n ≥ 1`:
  `Nonempty (CubeLaplacian.Syl2 (Fold.KBar n) ≃+ FoldGroup.twoM (CubeLaplacian.Syl2 (CubeLaplacian.K n)))`.
- **(DW′) The equivalent form.** For every `n ≥ 2` there are a type `H : Type` with `[AddCommGroup H]` and `[Finite H]` such that:
  - `Nonempty (CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+ (Fin (BaiCounts.aN n) → ZMod 2) × H)`;
  - `Nonempty (CubeLaplacian.Syl2 (Fold.KBar n) ≃+ FoldGroup.twoM H)`;
  - `BaiCounts.l0 H = BaiCounts.l1 H` (`H` has no cyclic factor `ℤ/2`).

## Part L — the layers of the folded cube

- **(L0)** For every abelian group `M`: `BaiCounts.l0 (FoldGroup.twoM M) = BaiCounts.l1 M`.
- **(L1)** For every `n ≥ 2`:
  `BaiCounts.l0 (CubeLaplacian.Syl2 (Fold.KBar n)) = 2 ^ (2 ^ (n - 1) - 1 - BaiCounts.aN n)`.

## Part R — the mod-2 layer

- **(R)** For every `n ≥ 2`:
  `Module.finrank (ZMod 2) (LinearMap.range (Fold.lapBar (ZMod 2) n)) = BaiCounts.aN n`.

## Proof sketch

- **(H)**:
  - write `lam = 2l + 1` or `lam = 2l + 2` (with `lam ≥ 1`, using `Nat.even_or_odd`);
  - `ZeroSmith.C5 l i` in the odd case, `EvenZero.TT l i` in the even case;
  - transport along the equality `lam = …` (`subst`).
- **(DW)**: `FoldGroup.P2 H n hn`.
- **(L0)**: unfold `l0`, `l1`, `twoPow`, `twoM`.
  - `2·(2M) = 4M` as subsets of `M`.
  - So the quotient `2M ⧸ 2(2M)` is `2M ⧸ (4M inside 2M)`, which is the quotient defining `l1 M`.
  - Write an explicit `AddEquiv` between the two quotients (`QuotientAddGroup.congr` with the equality of subgroups), then `Nat.card_congr`.
- **(L1)**:
  - (DW) and `l0_congr` give `l0 (Syl2 (KBar n)) = l0 (twoM (Syl2 (K n)))`;
  - (L0) turns this into `l1 (Syl2 (K n))`;
  - then `BaiCounts.B2 n hn`.
- **(DW′)**: let `S := Syl2 (K n)`, a finite abelian `2`-group.
  - **Decompose.** By the structure theorem for finite abelian groups (Mathlib `AddCommGroup.equiv_directSum_zmod_of_finite`, or its primed form), `S ≃+ ⨁_{j : ι} ZMod (2 ^ e_j)`, where every `e_j ≥ 1` (a factor with `e_j = 0` is trivial and can be dropped). The primes are all `2` because `S` is a `2`-group: every element has order a power of `2`.
  - **Split off the factors `ℤ/2`.** Split `ι` into `ι_1 := {j | e_j = 1}` and `ι_2 := {j | e_j ≥ 2}`, and take `H := ⨁_{j ∈ ι_2} ZMod (2 ^ e_j)`.
  - **Compute the layers.** For a cyclic group `ZMod (2^e)` with `e ≥ 1`, `l0 = 2`; and `l1 = 2` if `e ≥ 2`, `l1 = 1` if `e = 1`. Both layers are multiplicative over finite direct sums (C34 `l0_pi`, `l1_pi`).
  - **Count the factors `ℤ/2`.** From the layers, `|ι| = 2^{n−1} − 1` (`B1`) and `|ι_2| = 2^{n−1} − 1 − aN n` (`B2`). So `|ι_1| = aN n`, and `⨁_{ι_1} ZMod 2 ≃+ (Fin (aN n) → ZMod 2)`.
  - **The fold.** `twoM` commutes with products (C38b `P1`). `twoM (ZMod 2)` is trivial, and `twoM (ZMod (2^e)) ≃+ ZMod (2^(e−1))` for `e ≥ 1`. Hence `twoM S ≃+ twoM H`, and with (DW), `Syl2 (KBar n) ≃+ twoM H`.
  - **No factor `ℤ/2` in `H`.** `l0 H = l1 H = 2^{|ι_2|}`.

  (Any proof is fine; the statement is what matters.)
- **(R)**: let `N := 2^{n−1} = Fintype.card (Gbar n)` (needs `n ≥ 1`).
  - **The cokernel over `𝔽_2`.** `(Gbar n → ZMod 2) ⧸ range (lapBar (ZMod 2) n)` is the reduction mod 2 of `cokerBar n`, that is `cokerBar n ⊗[ℤ] ZMod 2`, by right exactness. C38b `K3` does the same over `ℤ_[2]`: copy its proof, with `ZMod 2` in place of `ℤ_[2]`.
  - **Its size.** `cokerBar n ≃ ℤ × KBar n` (`FoldGroup.cokerBarEquivKBar`), so the cokernel over `𝔽_2` has cardinality `2 · |KBar n / 2 KBar n|`.
  - **Only the `2`-part counts.** `|KBar n / 2 KBar n| = l0 (Syl2 (KBar n))`, because the odd part `T` satisfies `T = 2T`.
  - **Conclude.** By (L1), `dim_{𝔽_2} coker = 1 + (2^{n−1} − 1 − aN n) = N − aN n`. By rank–nullity (`LinearMap.finrank_range_add_finrank_ker`, or the quotient form `Submodule.finrank_quotient_add_finrank`), `finrank range = N − (N − aN n) = aN n`.

## Checks done before sending

- **Brute force `chkC51.py`.** It computes the direct `2`-adic Smith forms of the Laplacians of `Q_n` and of `Q_n/⟨𝟙⟩`, using the engine of the paper's `gate_direct.py` (plain integer elimination modulo `2^31`, independent of the dance). Range `n = 1, …, 10`. It checks:
  - (DW): one zero invariant factor each;
  - (DW′): the number of factors `ℤ/2` is `a_n`, and `H` has none;
  - (L1), with `l0 (Syl2 K)` and `l1`;
  - (R): the `𝔽_2`-rank of the folded Laplacian is `a_n`.
  - **66 checks, 0 failures.** Log `logs/chkC51.log`. The example of the paper at `n = 5` is reproduced: `{1: 6, 3: 4, 4: 1, 6: 4}` and `{2: 4, 3: 1, 5: 4}`.
- **Controls (all fire):**
  - the quotient by `x_1x_2` in place of the fold does not halve the group: 8 of 8 (`n = 3, …, 10`);
  - `a_n + 1` in place of `a_n` for the rank: 9 of 9;
  - the `𝔽_2`-rank of the cube Laplacian in place of the folded one is not `a_n`: 9 of 9.

## Notes

- After this piece only C52 remains: the odd parts (Bai's odd part of `K(Q_n)`, and [GMMY24, Proposition 1.9] for the folded cube, Corollary 1.4).
- (L0) is stated for every abelian group, because C52 or the final assembly may reuse it.
