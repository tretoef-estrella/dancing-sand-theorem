# Cleanliness: one move of the dance keeps the class (Theorem 10.15, paper v8 §10.5)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §10.5, Theorem 10.15 (cleanliness). This piece proves it for the covariant systems of C47, indexed by the dancers `Dn P`: the twist move is clean and lands again in the class with (a) and (b); the `V`-split keeps the class; the operators `2^α(D + c) + ηF + Σ_{m≥2} ζ_m F^{(m)}` with constant `ζ_m` are in the class at level `0`. Piece C48b transports this along `FormalDance.DanceRel` (the slots of `Fin` and the relabelling `Dance.splitIso`) and gives the dance of `XiOpZ`.

As in C47, the class is the rational class `Kr` (`𝒦_r`) in place of the paper's `𝒦`; the proof of Theorem 10.15 uses only the ring properties, shifts, inverses and `Θ` proved in C47.

Folder `RequestProject/Cleanliness/`, namespace `Cleanliness`. Nothing of the project is redefined.

## Setting (reused, without changing them)

- C47 `RingK`: `KRep`, `KRep.eval`, `Kr`, `S`, `theta`, `RS`, `oS`, `Dn`, `covSys`, `thetaSys`, `prodFun`, and (K1)–(K6), (S0)–(S5), (R1), (R2), (T0)–(T3).
- C40 `FormalOps`: `Bf`, `Bf.coef_mul`, `tw00`, `tw11`, `tw10`, `tw01`, `vplus`, `vprime`; C20 `Doubling.dfi` (`dfi s = Ring.inverse ((2s − 1)!!)`, so `dfi 0 = dfi 1 = 1`), and the instance `Doubling.OddUnits ℤ_[2]`.
- C40b `FormalDance`: `MAgree`, `twP`, `twC`, `twB`, `twD`, `vsplit`, `CleanStep`.
- C46 `Smith2.XiOpZ`.

Throughout, `A := ℤ_[2]`, and `Γ, Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]` are the coefficient functions of covariant systems (`Γ Δ m y`: the coefficient of `F^{(m)}` for `Δ = D \ D'` at the position `y`).

## Definitions (new)

1. `InK Γ : Prop := ∀ Δ m, Γ Δ m ∈ Kr`.
2. Condition (a): `PayA Γ : Prop := ∀ y, ∃ z, Γ ∅ 0 y = 4 * z` (the payments are `≡ 0 (mod 4)`).
3. Condition (b): `CoefB Γ : Prop := ∀ y, IsUnit (Γ ∅ 1 y)` (the diagonal coefficients of `F` are units).
4. `Good Γ : Prop := InK Γ ∧ PayA Γ ∧ CoefB Γ`.
5. The four blocks of the twist move at level `h` (`2^h` means `(2 : ℤ_[2]) ^ h`):
   - `GB Γ Δ q y := dfi q * Γ Δ (2 * q) y`;
   - `GC h Γ Δ q y := dfi q * Γ Δ (2 * q) (y + 2 ^ h)`;
   - `GP h Γ Δ q y := dfi (q + 1) * Γ Δ (2 * q + 1) (y + 2 ^ h)`;
   - `GD Γ Δ 0 y := 0` and `GD Γ Δ (q + 1) y := ((2 * q + 2 : ℕ) : ℤ_[2]) * dfi (q + 1) * Γ Δ (2 * q + 1) y`.
6. The `V`-split of the coefficient functions at level `h`:
   `vsplitG h Γ Δ m y := if h ∈ Δ then Γ (Δ.erase h) (m + 1) y else Γ Δ m y`.
7. For `P : Finset ℕ`, `h ∉ P`: the equivalence `splitDn P h hP : Dn P × Fin 2 ≃ Dn (insert h P)` with `(D, 0) ↦ D` and `(D, 1) ↦ insert h D` (its inverse is `D ↦ (D.erase h, if h ∈ D then 1 else 0)`).
8. The operator at level `0`: for `α : ℕ`, `η : ℤ_[2]`, `z : ℕ → ℤ_[2]`,
   `G0 α η z Δ m y := if Δ = ∅ then (if m = 0 then 2 ^ α * y else if m = 1 then η else z m) else 0`.

## Part W — the twist move

Fix `P : Finset ℕ`, `h : ℕ`, `c : ℤ_[2]`.

- **(W1) The blocks are covariant, one level up.** For every `Γ` (equalities in `Matrix (Dn P) (Dn P) (Bf ℤ_[2])`):
  `twB (covSys P h c Γ) = covSys P (h + 1) c (GB Γ)`, `twC (covSys P h c Γ) = covSys P (h + 1) c (GC h Γ)`, `twP (covSys P h c Γ) = covSys P (h + 1) c (GP h Γ)`, `twD (covSys P h c Γ) = covSys P (h + 1) c (GD Γ)`.
  (The level-`h` floors `2f` and `2f + 1` have the positions `2^{h+1} f + o_D + c` and that plus `2^h`.)
- **(W2) The blocks stay in the class.** If `InK Γ` then `InK (GB Γ)`, `InK (GC h Γ)`, `InK (GP h Γ)`, `InK (GD Γ)`; moreover `thetaSys (GB Γ) = thetaSys (GC h Γ)` and `thetaSys (GD Γ) = 0`.
- **(W3) The pivot is invertible in the class.** If `InK Γ` and `CoefB Γ`, there is `GQ` with `InK GQ`,
  `prodFun (h + 1) (GP h Γ) GQ = fun Δ m y => if Δ = ∅ ∧ m = 0 then 1 else 0`,
  `covSys P (h + 1) c (GP h Γ) * covSys P (h + 1) c GQ = 1`, `covSys P (h + 1) c GQ * covSys P (h + 1) c (GP h Γ) = 1`,
  and `GQ ∅ 0 y * Γ ∅ 1 (y + 2 ^ h) = 1` for every `y`.
- **(W4) Even payments make one move clean.** If `InK Γ`, `CoefB Γ` and `∀ y, ∃ z, Γ ∅ 0 y = 2 * z`, there is `Γ'` with `InK Γ'` and `CleanStep (covSys P h c Γ) (covSys P (h + 1) c Γ')`.
- **(W5) Theorem 10.15, the twist move.** If `Good Γ`, there is `Γ'` with `Good Γ'`, `CleanStep (covSys P h c Γ) (covSys P (h + 1) c Γ')`, and for every `y`:
  `2 * Γ' ∅ 0 y = -(Γ ∅ 0 y * Ring.inverse (Γ ∅ 1 (y + 2 ^ h)) * Γ ∅ 0 (y + 2 ^ h))` and `∃ z, Γ' ∅ 0 y = 8 * z`.

## Part V — the V-split

- **(V0)** `splitDn P h hP` is an equivalence, with `splitDn P h hP (D, 0) = ⟨D.1, _⟩` and `splitDn P h hP (D, 1) = ⟨insert h D.1, _⟩`.
- **(V1) The split system is covariant at the same level.** If `h ∉ P`, then for all `q q' : Dn P × Fin 2`:
  `vsplit (covSys P h c Γ) q q' = covSys (insert h P) h c (vsplitG h Γ) (splitDn P h hP q) (splitDn P h hP q')`.
  (The position of `(D ∪ {h}, g)` is `2^h (g + 1) + o_D + c = 2^h g + o_{D ∪ {h}} + c`; the new coupling from `D'` to `D ∪ {h}` has `Γ^{new}_{Δ ∪ {h}, m} = Γ_{Δ, m+1}`.)
- **(V2)** If `Good Γ` then `Good (vsplitG h Γ)`, for every `h`; and `vsplitG h Γ {h} 0 = Γ ∅ 1`.
- **(V3) Theorem 10.15, the split move.** If `h ∉ P` and `Good Γ`, there is `Γ'` with `Good Γ'` and
  `CleanStep (vsplit (covSys P h c Γ)) (fun q q' => covSys (insert h P) (h + 1) c Γ' (splitDn P h hP q) (splitDn P h hP q'))`.
- **(L1) Reindexing.** For `Fintype`s with `DecidableEq` and an equivalence `e : n ≃ n'`, and `G G' : Matrix n' n' (Bf A)` over any commutative ring `A`: `CleanStep G G' → CleanStep (fun j j' => G (e j) (e j')) (fun j j' => G' (e j) (e j'))`.

## Part O — the operators at level 0

- **(O1)** If `2 ≤ α` and `IsUnit η`, then `Good (G0 α η z)` for every `z`.
- **(O2)** For `α c : ℕ`, `η`, `z`: `covSys ∅ 0 (c : ℤ_[2]) (G0 α η z) ⟨∅, Finset.empty_subset _⟩ ⟨∅, Finset.empty_subset _⟩ = XiOpZ α c η (fun m _ => z m)`.

## Proof sketch

- (W1): coefficientwise, from the definitions of `tw00`, `tw11`, `tw10`, `tw01` and `covSys`: `2^h · (2f : ℤ) = 2^{h+1} f` and `2^h · (2f + 1) = 2^{h+1} f + 2^h`; outside `D' ⊆ D` both sides are `0`.
- (W2): (K3), (K4) (`dfi q` and `(2q + 2)` are constants); `thetaSys (GB Γ) = thetaSys (GC h Γ)` by (S2) with `e = −2^h`; each value of `GD` is `2 ×` an element of `Kr`, so its `theta` is `inl (red 2) * … = 0` (S1).
- (W3): `GP h Γ ∅ 0 y = Γ ∅ 1 (y + 2^h)` (`dfi 1 = 1`) is a unit for every `y`, so by (K6) a representation of `GP h Γ ∅ 0` has a unit constant and by (K5) `y ↦ Ring.inverse (GP h Γ ∅ 0 y)` is in `Kr`. Define `GQ Δ m` by well-founded recursion on `Δ.card + m`: `GQ Δ m y = Ring.inverse (GP h Γ ∅ 0 y) · (Γ₁ Δ m y − Σ_{(Δ₁, a) ≠ (∅, 0)} C(m, a) · GP h Γ Δ₁ a y · GQ (Δ \ Δ₁) (m − a) (y − a 2^{h+1} − o_{Δ₁}))`; it is in `Kr` by (K3), (K4). The term `(Δ₁, a) = (∅, 0)` of `prodFun` is `GP h Γ ∅ 0 y · GQ Δ m y`, so `prodFun (h + 1) (GP h Γ) GQ = Γ₁`. A left inverse `GL` by the mirror recursion (the term `(Δ₁, a) = (Δ, m)`, `GL Δ m y · GP h Γ ∅ 0 (y − m 2^{h+1} − o_Δ)`); with (T1) the matrices satisfy `L P = 1 = P Q`, hence `L = Q` and `Q P = 1`.
- (W4): Let `S := twD G − twB G · Q · twC G` with `G := covSys P h c Γ` and `Q := covSys P (h + 1) c GQ`. By (W1) and (T1), `S = covSys P (h + 1) c ΓS` with `ΓS := GD Γ − prodFun (h + 1) (prodFun (h + 1) (GB Γ) GQ) (GC h Γ)`, and `InK ΓS` (T2). By (T3) and (R1), in the commutative ring `RS`: `thetaSys ΓS = 0 − β · θQ · β = −(β · β) · θQ` with `β := thetaSys (GB Γ) = thetaSys (GC h Γ)` (W2). By (R2), `β · β` is `β ∅ 0 · β ∅ 0` at `(∅, 0)` and `0` elsewhere, and `β ∅ 0 = theta (Γ ∅ 0)` (`dfi 0 = 1`). A representation `r` of `Γ ∅ 0` has `r.a` even (by (K6), `r.a ≡ Γ ∅ 0 y ≡ 0 (mod 2)`), so `theta (Γ ∅ 0) * theta (Γ ∅ 0) = 0` by (S5). Hence `thetaSys ΓS = 0`, and by (S3) every `ΓS Δ m = 2 · ψ` with `ψ ∈ Kr`; put `Γ' Δ m := ψ` (chosen). Then `ΓS = 2 • Γ'`, `S = 2 • covSys P (h + 1) c Γ'` (T1), and `CleanStep` holds with `Q` (all `MAgree` from equalities).
- (W5): (W4), since (a) gives even payments. At `(∅, 0)` only the constant terms contribute (`prodFun` at `(∅, 0)` is a single product, and `GD Γ ∅ 0 = 0`): `ΓS ∅ 0 y = −Γ ∅ 0 y · GQ ∅ 0 y · Γ ∅ 0 (y + 2^h)` with `GQ ∅ 0 y = Ring.inverse (Γ ∅ 1 (y + 2^h))`; both payments are in `4ℤ_[2]`, so `ΓS ∅ 0 y ∈ 16ℤ_[2]` and `Γ' ∅ 0 y ∈ 8ℤ_[2]` (no 2-torsion), which is (a). At `(∅, 1)`: `GD Γ ∅ 1 y = 2 Γ ∅ 1 y`, and every term of the triple product at `(∅, 1)` contains `GB Γ ∅ 0` or `GC h Γ ∅ 0` (the order `m = 1` is split among three factors), each in `4ℤ_[2]`; so `ΓS ∅ 1 y = 2 Γ ∅ 1 y + 4 w` and `Γ' ∅ 1 y = Γ ∅ 1 y + 2 w` is a unit, which is (b).
- (V1): coefficientwise from `vsplit`, `vplus`, `vprime` and `covSys`, with `h ∉ D` for `D ⊆ P`, `oS (insert h D) = oS D + 2^h` (T0), `insert h D' ⊆ D` false, `D' ⊆ insert h D ↔ D' ⊆ D`, `insert h D \ insert h D' = D \ D'`, `insert h D \ D' = insert h (D \ D')`.
- (V2): the entries at `Δ = ∅` do not change (`h ∉ ∅`). (V3): (V1), (V2), (W5) for `insert h P` at level `h`, and (L1) with `splitDn`.
- (L1): the tw maps act entrywise, so they commute with reindexing; products of reindexed matrices are reindexed products (`Matrix.submatrix_mul_equiv`), and `1` reindexes to `1`; take `Q ∘ (e, e)`.
- (O1): `y ↦ 2^α y ∈ Kr` for `α ≥ 2` (K3) with constant `0`; constants are in `Kr`; `0 ∈ Kr`. (O2): coefficientwise, `2^0 · f + oS ∅ + c = f + c`.

## Checks before formalization

`chkC48.py` (exact rationals; elements of `ℤ_2` as fractions with odd denominators; random representations in the class with small coefficients; `P ⊆ {0, 1, 2}`, `h ≤ 3`, random shifts `c`, floors `−2…4`, orders `m < 3`): (W1) the four block identities entry by entry; (W3) the recursive inverse, `prodFun = Γ₁` at sample positions, `P Q = 1` and `Q P = 1` as matrices over `Dn P`, integrality; (W4) every value of `ΓS` even; (W5) the formula for `Γ' ∅ 0`, `Γ' ∅ 0 ≡ 0 (mod 8)`, `Γ' ∅ 1` a unit; the matrix identity `twD − twB Q twC = covSys(ΓS)`; (V1) the split identity in all four blocks; (V2); (O2) for `α = 2, 3`, `c = 0…3`. 24 493 checks, 0 failures. Controls, all five fire: the block `C` without the shift `2^h` breaks (W1); the split without the new `2^h` in the position breaks (V1); an even diagonal coefficient of `F` makes the inverse of the pivot non-integral; an odd payment makes `ΓS` odd somewhere (not clean); a payment `≡ 2 (mod 4)` keeps the move clean but loses (a) or (b) at the next level.

Note from the checks: within one move an even payment suffices for cleanliness — that is (W4); the condition `≡ 0 (mod 4)` of the paper is what keeps (a) and (b) one level up — that is (W5).
