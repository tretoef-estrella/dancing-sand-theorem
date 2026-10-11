module

public import RequestProject.InvBlock.All

/-!
# `C42_floors_and_corollary_10_9.md`: Definitions (new) — `slotOf`, `inIdx`, `outIdx`

Namespace `InvFloors`. Reused, not redefined: C13 `Dance.slots`; C18 `DPLattice`; C20
`Doubling.phi`; C23 `tensorV`; C29 `Filt.T`; C32 `Families.ds`; C40d `FormalProp.splitEquiv`;
C41 `InvBlock.inH`, `outH`, `castLat`, `ri`, `slots_zero`, `slots_succ_pos`, `slots_succ_neg`,
`T_succ_pos`, `T_succ_neg`.

* `slotOf l r : Fin (Dance.slots (Families.ds l) r) → Fin r` and
  `ioIdx b l r : Fin (Dance.slots (Families.ds l) r) → (T A l).ι` (`b : Fin 2`) are defined by
  the same well-founded recursion along `l` as `InvBlock.inH`, `InvBlock.outH`:
  - `l = 0`: `slotOf = Fin.cast`, `ioIdx b = ()` (the basis of `T A 0 = one A` is `Unit`);
  - twist step (`l = n + 1`, `n` even, `l' = n / 2`): `slotOf = slotOf'`, `ioIdx b = (b, ioIdx' b)`
    in `Fin 2 × (T A l').ι`;
  - split step (`l = n + 1`, `n` odd, `l' = n / 2`, `r * 2` slots one level down): with
    `(s, a) = FormalProp.splitEquiv r (slotOf' j)` (the slot pair of `vpack`), `slotOf = s` and
    `ioIdx b = (a, (b, ioIdx' b))` in `Fin 2 × (Fin 2 × (T A l').ι)`.
  The slots are reindexed along `Fin.cast` (as `InvBlock.ri`), the basis indices along the
  equalities of lattices by `castIdx` (as `InvBlock.castLat`).
* `inIdx l r := ioIdx 0 l r` (the index `(0, i)` at a twist step), `outIdx l r := ioIdx 1 l r`
  (the index `(1, i)`). All three depend only on `l` and `r`.
-/

@[expose] public section

noncomputable section

namespace InvFloors

open DPLattice Doubling Filt FormalOps FormalDance FormalAct InvBlock

variable {A : Type*} [CommRing A]

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, Definitions): transport of a basis index along
an equality of lattices `N = N'` (the index form of `InvBlock.castLat`). -/
def castIdx {N N' : DPLattice A} (h : N = N') : N.ι → N'.ι :=
  Eq.rec (motive := fun N' _ => N.ι → N'.ι) id h

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, (F4)–(F5)): `castIdx` keeps the weight. -/
@[simp] lemma wt_castIdx {N N' : DPLattice A} (h : N = N') (i : N.ι) :
    N'.wt (castIdx h i) = N.wt i := by
  subst h; rfl

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, (F1)): `castLat` sends a basis vector to the
basis vector of the transported index. -/
lemma castLat_single {N N' : DPLattice A} (h : N = N') {n : Type*} {_ : DecidableEq n} (s : n)
    (i : N.ι) :
    castLat h n (Pi.single s (Pi.single i 1)) = Pi.single s (Pi.single (castIdx h i) 1) := by
  subst h; rfl

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, (F2)): `castLat⁻¹` reads at the transported
index. -/
lemma castLat_symm_read {N N' : DPLattice A} (h : N = N') {n : Type*} (w : n → N'.ι → A) (s : n)
    (i : N.ι) : (castLat h n).symm w s i = w s (castIdx h i) := by
  subst h; rfl

/-- **Definitions (new)** of `C42_floors_and_corollary_10_9.md`: the slot of a final slot,
`slotOf l r : Fin (Dance.slots (Families.ds l) r) → Fin r`, by the recursion of `InvBlock.inH`
(`l = 0`: `Fin.cast`; twist step: unchanged; split step: the first component of
`FormalProp.splitEquiv r`). It depends only on `l` and `r`. -/
def slotOf : (l r : ℕ) → Fin (Dance.slots (Families.ds l) r) → Fin r
  | 0, r => fun j => Fin.cast (slots_zero r) j
  | n + 1, r =>
      if h : n % 2 = 0 then fun j => slotOf (n / 2) r (Fin.cast (slots_succ_pos h r) j)
      else fun j => (FormalProp.splitEquiv r (slotOf (n / 2) (r * 2)
        (Fin.cast (slots_succ_neg h r) j))).1
decreasing_by all_goals omega

variable [IsDomain A] [CharZero A] [OddUnits A]

/-- **Definitions (new)** of `C42_floors_and_corollary_10_9.md`, the common recursion of `inIdx`
(`b = 0`) and `outIdx` (`b = 1`): `ioIdx b l r : Fin (Dance.slots (Families.ds l) r) → (T A l).ι`,
by the recursion of `InvBlock.inH`, `InvBlock.outH` (`l = 0`: `()`; twist step: `(b, i)` in
`Fin 2 × ι`; split step: `(a, (b, i))` with `a` the second component of
`FormalProp.splitEquiv r`, through `vpack`). It depends only on `b`, `l` and `r`. -/
def ioIdx (b : Fin 2) : (l r : ℕ) → Fin (Dance.slots (Families.ds l) r) → (T A l).ι
  | 0, _ => fun _ => castIdx (T_zero (A := A)).symm (() : (one A).ι)
  | n + 1, r =>
      if h : n % 2 = 0 then fun j =>
        castIdx (T_succ_pos A h).symm
          ((b, ioIdx b (n / 2) r (Fin.cast (slots_succ_pos h r) j)) : (phi (T A (n / 2))).ι)
      else fun j =>
        castIdx (T_succ_neg A h).symm
          (((FormalProp.splitEquiv r (slotOf (n / 2) (r * 2) (Fin.cast (slots_succ_neg h r) j))).2,
            ((b, ioIdx b (n / 2) (r * 2) (Fin.cast (slots_succ_neg h r) j)) :
              (phi (T A (n / 2))).ι)) : (tensorV (phi (T A (n / 2)))).ι)
decreasing_by all_goals omega

/-- **Definitions (new)** of `C42_floors_and_corollary_10_9.md`: the coordinate index
`inIdx l r : Fin (Dance.slots (Families.ds l) r) → (T A l).ι` (twist step: `(0, i)`; split step:
`(a, (0, i))` through `vpack` and `FormalProp.splitEquiv`). It depends only on `l` and `r`. -/
def inIdx (l r : ℕ) : Fin (Dance.slots (Families.ds l) r) → (T A l).ι := ioIdx 0 l r

/-- **Definitions (new)** of `C42_floors_and_corollary_10_9.md`: the source index
`outIdx l r : Fin (Dance.slots (Families.ds l) r) → (T A l).ι` (twist step: `(1, i)`; split step:
`(a, (1, i))` through `vpack` and `FormalProp.splitEquiv`). It depends only on `l` and `r`. -/
def outIdx (l r : ℕ) : Fin (Dance.slots (Families.ds l) r) → (T A l).ι := ioIdx 1 l r

end InvFloors
