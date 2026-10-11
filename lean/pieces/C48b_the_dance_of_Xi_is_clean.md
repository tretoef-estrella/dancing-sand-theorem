# The dance of Ξ is clean, and Theorem 10.16 for c ≥ 1 (paper v8 §10.5)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §10.5, Theorem 10.16, the case `c ≥ 1` (and the family `l = 0` for every `c`). Piece C48 proved one move of the dance on covariant systems indexed by the dancers `Dn P`. This piece transports it along `FormalDance.DanceRel`, whose slots are `Fin r` and whose split moves are relabelled by `Dance.splitIso`: the dance of `2^α(D + c) + ηF + Σ_{m≥2} z_m F^{(m)}` (constants `z_m`, `η` a unit, `α ≥ 2`) is clean along every word `ds`. With C46 (R5) this gives `coker(Ξ on T(l)) ≅ X^{(α)}(l, c)` for `c ≥ 1`. The case `c = 0`, `l ≥ 1` (continuity in `c`) is a later piece.

Folder `RequestProject/DanceXi/`, namespace `DanceXi`. Nothing of the project is redefined.

## Setting (reused, without changing them)

- C48 `Cleanliness`: `Good`, `splitDn`, `G0`, and (V0), (V3), (W5), (L1), (O1), (O2).
- C47 `RingK`: `Dn`, `covSys`.
- C40 `FormalOps`: `Bf`, `vplus`, `vprime`. C40b `FormalDance`: `MAgree`, `vsplit`, `CleanStep`, `DanceRel`.
- C13 `Dance`: `slots`, `splitIso`.
- C46 `Smith2`: `XiOpZ`, (R5).
- C40c `FormalAct.sysAct`; C40d `FormalProp.Q2_zero`; C29 `Filt.T`, `Filt.T_zero`; C32 `Families.ds`; C16 `FamilyGroup.X`; C13 `Dance.SysT`, `Dance.sigma`, `Dance.F`, `Dance.pσ`, `Dance.κσ`; C11 `Payment.G`.

## Part T — transport along the dance

- **(T1) The `V`-split commutes with reindexing.** For any commutative ring `A`, `Fintype`s `n, n'` with `DecidableEq`, `e : n ≃ n'` and `G : Matrix n' n' (Bf A)`:
  `vsplit (fun j j' => G (e j) (e j')) = fun q q' => vsplit G (e q.1, q.2) (e q'.1, q'.2)`.
- **(T2) Transport.** For every `ds : List Bool`, `r h : ℕ`, `P : Finset ℕ` with `∀ t ∈ P, t < h`, `c : ℤ_[2]`, `Γ` with `Cleanliness.Good Γ`, `e : Fin r ≃ Dn P` and `G : Matrix (Fin r) (Fin r) (Bf ℤ_[2])` with `G = fun j j' => covSys P h c Γ (e j) (e j')`: there is `Gk` with `DanceRel ds r G Gk`.
- **(T3) The dance of `Ξ`.** For every `ds : List Bool`, `α c : ℕ` with `2 ≤ α`, `η : ℤ_[2]` with `IsUnit η`, and `z : ℕ → ℤ_[2]`: there is `GkZ` with `DanceRel ds 1 (fun _ _ => Smith2.XiOpZ α c η (fun m _ => z m)) GkZ`.

## Part R — Theorem 10.16 for `c ≥ 1`

- **(R0) The family `l = 0`, every `c`.** For `α c : ℕ` with `1 ≤ α`, every `η : ℤ_[2]`, every `ζ : ℕ → ℤ → ℤ_[2]` and every `B ≥ 1`:
  `Nonempty (((Fin 1 → (Filt.T ℤ_[2] 0).ι → ℤ_[2]) ⧸ LinearMap.range (FormalAct.sysAct (Filt.T ℤ_[2] 0) (0 : ℤ) B (fun _ _ => Smith2.XiOpZ α c η ζ))) ≃ₗ[ℤ_[2]] FamilyGroup.X (Families.ds 0) α c)`.
- **(R1) `l ≥ 1`, `c ≥ 1`.** For `1 ≤ l`, `2 ≤ α`, `1 ≤ c`, `IsUnit η`, `z : ℕ → ℤ_[2]` and every `B ≥ l + 1`:
  `Nonempty (((Fin 1 → (Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸ LinearMap.range (FormalAct.sysAct (Filt.T ℤ_[2] l) (l : ℤ) B (fun _ _ => Smith2.XiOpZ α c η (fun m _ => z m)))) ≃ₗ[ℤ_[2]] FamilyGroup.X (Families.ds l) α c)`.
- **(R2) Theorem 10.16 for `c ≥ 1`.** For every `l`, `2 ≤ α`, `1 ≤ c`, `IsUnit η`, `z : ℕ → ℤ_[2]` and every `B ≥ l + 1`: the same isomorphism as in (R1).

## Proof sketch

- (T1): entry by entry from the definition of `vsplit` (the case split is on `q.2`, `q'.2` only).
- (T2): induction on `ds`, generalizing `r, h, P, Γ, e, G`.
  - `[]`: take `Gk := G` (`MAgree` is reflexive).
  - `false :: rest`: by (W5) there is `Γ'` with `Good Γ'` and `CleanStep (covSys P h c Γ) (covSys P (h + 1) c Γ')`; by (L1) along `e`, `CleanStep G (fun j j' => covSys P (h + 1) c Γ' (e j) (e j'))`. The hypothesis `∀ t ∈ P, t < h + 1` holds; apply the induction hypothesis with `h + 1`, the same `P` and `e`.
  - `true :: rest`: `h ∉ P` (every `t ∈ P` is `< h`). By (V3) there is `Γ'` with `Good Γ'` and `CleanStep (vsplit (covSys P h c Γ)) (fun q q' => covSys (insert h P) (h + 1) c Γ' (splitDn P h hP q) (splitDn P h hP q'))`. By (T1), `vsplit G` is that `vsplit` reindexed along `Equiv.prodCongr e (Equiv.refl _)`, so by (L1) `CleanStep (vsplit G) G''` with `G'' q q' := covSys (insert h P) (h + 1) c Γ' (splitDn P h hP (e q.1, q.2)) (splitDn P h hP (e q'.1, q'.2))`. The matrix of `DanceRel` for `rest` is `fun j j' => G'' (ofLex ((Dance.splitIso r).symm j)) (ofLex ((Dance.splitIso r).symm j'))`, which is `covSys (insert h P) (h + 1) c Γ'` reindexed along the equivalence `e₂ : Fin (r * 2) ≃ Dn (insert h P)` obtained by composing `(Dance.splitIso r).symm.toEquiv`, `ofLex`, `Equiv.prodCongr e (Equiv.refl _)` and `splitDn P h hP`. Every `t ∈ insert h P` is `< h + 1`; apply the induction hypothesis with `r * 2`, `h + 1`, `insert h P`, `Γ'`, `e₂`.
- (T3): (T2) with `r = 1`, `h = 0`, `P = ∅`, `c := (c : ℤ_[2])`, `Γ := G0 α η z` (good by (O1)), `e` the unique equivalence `Fin 1 ≃ Dn ∅`; the hypothesis on `G` is (O2), since both slots are the unique element of `Dn ∅`.
- (R0): `Filt.T ℤ_[2] 0 = one` (`T_zero`), and by `Q2_zero` the cokernel is that of the `1 × 1` matrix `finalM (fun _ _ => XiOpZ α c η ζ)`, whose entry is `(XiOpZ α c η ζ).coef 0 0 = 2^α · (0 + c) = 2^α c`. On the other side, `Families.ds 0 = []`, `Dance.Idx [] = Unit`, `Dance.F ℤ_[2] [] = 0`, so `Dance.sigma ℤ_[2] [] α c` is multiplication by `2 · pσ α c 0 0 = 2 · 2^{α−1} · c = 2^α c` (here `1 ≤ α`) on `SysT ℤ_[2] [] (Fin 1)`, a free module of rank one. Both cokernels are `ℤ_[2] ⧸ (2^α c)`.
- (R1): (T3) with `ds := Families.ds l` gives the hypothesis `hG` of C46 (R5); apply (R5).
- (R2): (R0) for `l = 0` (with `ζ := fun m _ => z m`, `1 ≤ α` from `2 ≤ α`), (R1) for `l ≥ 1`.

## Checks before formalization

`chkC48b.py` (exact rationals; the lattice model of `chkC43.py`; elements of `ℤ_2` as fractions with odd denominators). For `l = 0…9`, `α = 2, 3`, `c = 1, 2, 3`, four random units `η` and random constant `z_m` each (240 cells): the dance of `Ξ` is run on the lattice `T(l)` itself, with the twist/split indexing of `chkC43.lift`; at every move the pivot is invertible over `ℤ_2` and the Schur complement is `2 ×` an integral matrix (clean); the number of moves is the length of `ds l`; the final matrix is integral with the Smith form of `σ`'s final matrix; and the Smith form of `Ξ` on `T(l)` equals that of `σ = 2^α(D + c) + F` (Theorem 10.16). For `l = 0`: `Ξ` on `T(0)` is the `1 × 1` matrix `2^α c`, also for `c = 0` (the zero map). 1 286 checks, 0 failures. The same run with `c = 0` (80 cells, Smith comparisons left out since `σ_0` is singular): every move clean, 270 checks, 0 failures — (T3) has no condition on `c`. Controls, all three fire: `η = 2` (not a unit); comparison with the shift `c + 1`; `α = 1` (payments only `≡ 2 (mod 4)`).
