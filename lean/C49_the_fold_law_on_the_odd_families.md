# The fold law on the odd families: Corollary 10.17 for j ≥ 1, and for l = 0 (paper v8 §10.6)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §10.2 and §10.6, Corollary 10.17: for every `l ≥ 0` and every `j ≥ 0`, `X̄(2l + 1, j) ≅ 2X(2l + 1, j)`. This piece proves it for every `l` and every `j ≥ 1`, and for `l = 0` and every `j`. The remaining case (`j = 0`, `l ≥ 1`, which needs Theorem 10.16 at `c = 0`, proved in the paper by continuity in `c`) is a later piece.

What is new here is the link between the concrete operators on `T(l)` of C39 (`FoldHalf.Psi`, the paper's `Ψ_j`) and C39b (`FoldCube.SigmaOp`, the paper's `Σ_c`) and the formal operators of C40: both are the action of an element of `Bf ℤ_[2]` of the form `Smith2.XiOpZ 2 c η (fun m _ => z m)`, so C48b (R2) and (R0) apply to both.

Folder `RequestProject/FoldOdd/`, namespace `FoldOdd`. Nothing of the project is redefined.

## Setting (reused, without changing them)

- C40 `FormalOps`: `Bf` (its ring structure, `Bf.dg`, `Bf.fd`, the product `(x * y).coef m f = Σ_{a ∈ range (m + 1)} C(m, a) * x.coef a f * y.coef (m − a) (f − a)`), `flD`, `act`, and the theorems `act_one`, `act_add`, `act_smul`, `act_mul`, `act_fd`, `act_dg`, `act_bound`, `B4`.
- C40c `FormalAct.sysAct`.
- C20 `Doubling.OddUnits`, `Doubling.dfi`.
- C39 `FoldHalf`: `Ch`, `Sh`, `parOp`, `ShInv`, `Psi`, (S1), (S2), (A3), (A4_odd).
- C39b `FoldCube`: `SigmaOp`, (O4), (O5_X).
- C46 `Smith2.XiOpZ`. C48b `DanceXi`: (R0), (R2).
- C38b `FoldGroup.XbarFam`, `FoldGroup.twoM`; C29 `Filt.T`; C32 `Families.ds`; C16 `FamilyGroup.X`; C18 `DPLattice`, `H`.

## Definitions (new)

For a commutative ring `A`:
- `cst (a : ℕ → A) : Bf A := ⟨fun m _ => a m⟩` (a series in `F` with constant coefficients).
- `chC m := Doubling.dfi m`, `shC m := Doubling.dfi (m + 1)` (as functions `ℕ → A`).
- `shInvC : ℕ → A` by strong recursion: `shInvC 0 = 1` and, for `m ≥ 1`, `shInvC m = − Σ_{b ∈ range m} C(m, b) * shC (m − b) * shInvC b`. (Any definition is fine if these two equations are proved as lemmas.)
- `ChF := cst chC`, `ShF := cst shC`, `ShInvF := cst shInvC` (in `Bf A`).

Over `ℤ_[2]`, for `j c : ℕ`:
- `KF j := (ChF − ((−1 : ℤ_[2]) ^ j) • (1 : Bf ℤ_[2])) * ShInvF` and `kJ j m := (KF j).coef m 0`.
- `PsiF j := Bf.dg (fun f => 4 * (f : ℤ_[2]) + 2 * (j : ℤ_[2])) + KF j` (the paper's `Ψ_j = 2(2D + j) + (Ch − (−1)^j)·Sh^{−1}`).
- `SigF c := Bf.dg (fun f => 4 * ((f : ℤ_[2]) + c)) + Bf.fd 1` (the paper's `Σ_c = F + 4(D + c)`).

## Part F — the formal operators

- **(F1) Constant series.** For `a b : ℕ → A`: `cst a * cst b = cst (fun m => Σ_{a' ∈ range (m + 1)} C(m, a') * a a' * b (m − a'))`, and `cst a * cst b = cst b * cst a`.
- **(F2) `Sh` is a unit.** `ShF * ShInvF = 1` and `ShInvF * ShF = 1` (in `Bf A`, any commutative ring `A`).
- **(F3) The action.** Let `N : DPLattice A`, `W : ℤ`, `BN B : ℕ` with (nil) `∀ s ≥ BN, N.Fd s = 0`, `BN ≤ B` and `1 ≤ B`. Then
  `act N W B ChF = FoldHalf.Ch N BN`, `act N W B ShF = FoldHalf.Sh N BN`, and `act N W B ShInvF = FoldHalf.ShInv N BN`.
- **(F4) `Ψ_j` and `Σ_c` on `T(l)`.** For `l j c B : ℕ` with `l + 1 ≤ B`, over `ℤ_[2]`:
  `act (Filt.T ℤ_[2] l) (l : ℤ) B (PsiF j) = FoldHalf.Psi (Filt.T ℤ_[2] l) ((l : ℤ) + j) (l + 1)` and
  `act (Filt.T ℤ_[2] l) (l : ℤ) B (SigF c) = FoldCube.SigmaOp (Filt.T ℤ_[2] l) ((l : ℤ) + 2 * (c : ℤ))`.
- **(F5) Both are of the form `Ξ`.** For every `j c : ℕ`:
  `PsiF j = Smith2.XiOpZ 2 ((j + 1) / 2) (kJ j 1) (fun m _ => kJ j m)` and `IsUnit (kJ j 1)`; moreover `kJ j 1 = 1` if `Even j` and `3 * kJ j 1 = 1` if `Odd j`.
  `SigF c = Smith2.XiOpZ 2 c 1 (fun _ _ => 0)`.
- **(F6) One slot.** For `N : DPLattice A`, `W : ℤ`, `B : ℕ` and `x : Bf A`:
  `Nonempty (((Fin 1 → N.ι → A) ⧸ LinearMap.range (FormalAct.sysAct N W B (fun _ _ => x))) ≃ₗ[A] ((N.ι → A) ⧸ LinearMap.range (act N W B x)))`.

## Part C — Corollary 10.17

- **(C1) The two cokernels on `T(l)`.** For `l j : ℕ` with `1 ≤ j ∨ l = 0`:
  `Nonempty (((Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸ LinearMap.range (FoldHalf.Psi (Filt.T ℤ_[2] l) ((l : ℤ) + j) (l + 1)) ≃ₗ[ℤ_[2]] ((Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸ LinearMap.range (FoldCube.SigmaOp (Filt.T ℤ_[2] l) ((l : ℤ) + 2 * (((j + 1) / 2 : ℕ) : ℤ))))`.
- **(C2) Corollary 10.17 for `j ≥ 1`.** For every `l j : ℕ` with `1 ≤ j`:
  `Nonempty (FoldGroup.XbarFam (2 * l + 1) j ≃+ FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 1)) 1 j))`.
- **(C3) Corollary 10.17 for `l = 0`.** For every `j : ℕ`:
  `Nonempty (FoldGroup.XbarFam (2 * 0 + 1) j ≃+ FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * 0 + 1)) 1 j))`.

## Proof sketch

- (F1): by `Bf.ext` and the product formula; the shift `f − a` does not matter because the coefficients do not depend on `f`; commutativity by `a' ↦ m − a'` and `C(m, a') = C(m, m − a')`.
- (F2): by (F1), `ShF * ShInvF = cst g` with `g m = Σ_{a'} C(m, a') shC a' shInvC (m − a')`; `g 0 = shC 0 * shInvC 0 = dfi 1 = 1` (`(2·1 − 1)!! = 1`), and for `m ≥ 1` the recursion of `shInvC` (reindexed by `b = m − a'`, with `shC 0 = 1`) gives `g m = 0`. The other order by the commutativity of (F1).
- (F3): `act N W B (cst a) = Σ_{m ∈ range B} flD N W (fun _ => a m) * N.Fd m = Σ_{m ∈ range B} a m • N.Fd m`; terms with `m ≥ BN` vanish by (nil), so this is `Σ_{s ∈ range BN} a s • N.Fd s` — `Ch` and `Sh` by their definitions. For `ShInvF`: by `act_mul`, `act_one` and (F2), `act ShInvF` is a two-sided inverse of `act ShF = Sh`, so it equals `Ring.inverse (Sh N BN) = ShInv N BN`.
- (F4): by (A3), `T(l)` has (nil) with `BN = l + 1`, and by (O4) every weight `w` of `T(l)` has `w ≤ l` and `Even (l − w)`. `act` is additive and multiplicative (`act_add`, `act_mul`, `act_smul`, `act_one`, `act_dg`, `act_fd`). `act (Bf.dg p) = flD (T l) l p` multiplies the coordinate of weight `w` by `p ((l − w) / 2)`; with `p f = 4f + 2j` and `l − w` even this is `2(l − w) + 2j = 2(l + j) − 2w`, i.e. `((2 * (l + j) : ℤ) : ℤ_[2]) • 1 − 2 • H`. The scalar `(−1)^j • 1` acts as `(−1)^j • 1`, and `parOp (T l) (l + j)` multiplies the coordinate of weight `w` by `(−1)^{|l + j − w|} = (−1)^j` (`l − w` even), so it is `(−1)^j • 1`. With (F3) this is `Psi`. For `SigF`: `flD` of `4(f + c)` is `2(l − w) + 4c = 2(l + 2c) − 2w`, and `act (Bf.fd 1) = N.Fd 1`.
- (F5): coefficient by coefficient (`Bf.ext`). For `m ≥ 1`, `Bf.dg` contributes nothing and `(KF j).coef m f` does not depend on `f` (constant series, (F1)), so it equals `kJ j m`. For `m = 0`: `(KF j).coef 0 f = (chC 0 − (−1)^j) * shInvC 0 = 1 − (−1)^j`, and `4f + 2j + 1 − (−1)^j = 4(f + (j + 1)/2)` (even and odd `j` separately). `kJ j 1 = C(1,0)(chC 0 − (−1)^j) shInvC 1 + C(1,1) chC 1 shInvC 0` with `chC 0 = chC 1 = 1`, `shInvC 1 = −dfi 2 = −⅟3`: `kJ j 1 = 1` for even `j`, `= 1 − 2·⅟3 = ⅟3` for odd `j`; both units (`OddUnits ℤ_[2]`, or `3` is a unit in `ℤ_[2]`). `SigF c`: directly.
- (F6): `Fin 1 → M ≃ M` (`LinearEquiv.funUnique`), and under it `sysAct N W B (fun _ _ => x)` becomes `act N W B x` (the sum over `s' : Fin 1` has one term); transport the range.
- (C1): with `c := (j + 1) / 2` and `B := l + 1`: by (F4) and (F5), `Psi … = act (T l) l B (XiOpZ 2 c (kJ j 1) (fun m _ => kJ j m))` and `SigmaOp … = act (T l) l B (XiOpZ 2 c 1 (fun _ _ => 0))`. By (F6), each cokernel is the cokernel of the `sysAct` on `Fin 1`. If `1 ≤ j` then `1 ≤ c`, and C48b (R2) (`α = 2`, `η = kJ j 1` resp. `1`, `z = kJ j ·` resp. `0`) gives `≅ FamilyGroup.X (Families.ds l) 2 c` for both; if `l = 0`, C48b (R0) (`α = 2 ≥ 1`) gives the same for both, for every `c`. Compose.
- (C2), (C3): `XbarFam (2l + 1) j ≃ₗ coker(Psi (T l) (l + j) (l + 1))` by C39 (A4_odd); then (C1); then C39b (O5_X), read backwards: `coker(SigmaOp (T l) (l + 2c)) ≃+ twoM (FamilyGroup.X (Families.ds (2l + 1)) 1 j)`. Compose the additive equivalences.

## Checks before formalization

`chkC49.py` (exact rationals; the lattice model of `T(l)` of `chk_lattice_lib.py`; `F^{(m)} = F^m / m!`). Constant series up to `m = 13`: `Sh · Sh^{−1} = 1 = Sh^{−1} · Sh` with the recursion above. For `j = 0…11`: `kJ j 0 = 1 − (−1)^j`; `kJ j 1 = 1` (even `j`) or `1/3` (odd `j`), a 2-adic unit; every `kJ j m` 2-adically integral; `PsiF j = XiOpZ 2 ((j + 1)/2) (kJ j 1) (kJ j ·)` coefficient by coefficient on floors `−6…11`. `SigF c = XiOpZ 2 c 1 0` for `c = 0…7`. On `T(l)`, `l = 0…6`: every weight `w` has `−l ≤ w ≤ l` and `l − w` even; `act (PsiF j)` (floor `(l − w)/2` of the target, bounds `B = l + 1` and `l + 3`) equals C39's `Psi (T l) (l + j) (l + 1)` exactly, and `act (SigF c)` equals C39b's `SigmaOp (T l) (l + 2c)`, `j = 0…5`; the 2-adic Smith forms of `Psi (T l) (l + j)` and `SigmaOp (T l) (l + 2⌈j/2⌉)` agree (Corollary 10.17; also at `j = 0`, the case left for the later piece). 288 checks, 0 failures; `logs/chkC49.log`. Controls, all four fire: `Psi` at `d = l + j + 1` differs from `act (PsiF j)` (78 cells); the Smith form of `SigmaOp` at `c + 1` differs (31 cells); `XiOpZ` at the shift `c + 1` differs (31 cells); `η = 2` is not a unit.
