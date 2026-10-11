module

public import RequestProject.Stability.Basic
public import RequestProject.Windows.All
public import RequestProject.Deficit.All

/-!
# `C44_stability_and_rigidity.md`, Part A: the definitions `nest`, `Amat`, `nuA`

Namespace `Stability`. For `ds : List Bool`, `k := ds.length`, the final slots are
`Fin (Dance.slots ds 1)` and `D_s := Windows.Dset ds s` (read through `s.val`). Reused
(not redefined): C14 `Windows.Dset`, `Windows.Ids`; C10 `Deficit.a`; C3 `Rulers.delta`.

* `nest ds s s'` is `D_{s'} ⊆ D_s`;
* `Amat ds s s'` is `a_k(D_s ∖ D_{s'})` (C10's `Deficit.a (Windows.Ids ds) k`, cast to `ℚ_[2]`)
  on nested pairs and `0` elsewhere;
* `nuA ds s s'` is `(Rulers.delta k (D_s ∖ D_{s'})).toNat`.
-/

@[expose] public section

noncomputable section

namespace Stability

/-- `C44_stability_and_rigidity.md`, Part A: the nesting relation
`nest ds s s' := Windows.Dset ds s' ⊆ Windows.Dset ds s` on `Fin (Dance.slots ds 1)`. -/
def nest (ds : List Bool) (s s' : Fin (Dance.slots ds 1)) : Prop :=
  Windows.Dset ds s' ⊆ Windows.Dset ds s

/-- `C44_stability_and_rigidity.md`, Part A: `nest ds` is decidable. -/
instance (ds : List Bool) : DecidableRel (nest ds) := fun s s' =>
  inferInstanceAs (Decidable (Windows.Dset ds s' ⊆ Windows.Dset ds s))

/-- `C44_stability_and_rigidity.md`, Part A: the matrix `𝒜` of the word,
`Amat ds s s' := if nest ds s s' then a_k(D_s ∖ D_{s'}) else 0` (in `ℚ_[2]`, `k = ds.length`). -/
def Amat (ds : List Bool) : Matrix (Fin (Dance.slots ds 1)) (Fin (Dance.slots ds 1)) ℚ_[2] :=
  Matrix.of fun s s' => if nest ds s s' then
    ((Deficit.a (Windows.Ids ds) ds.length (Windows.Dset ds s \ Windows.Dset ds s') : ℤ) : ℚ_[2])
    else 0

/-- `C44_stability_and_rigidity.md`, Part A: the weights
`nuA ds s s' := (Rulers.delta k (D_s ∖ D_{s'})).toNat` (`k = ds.length`). -/
def nuA (ds : List Bool) (s s' : Fin (Dance.slots ds 1)) : ℕ :=
  (Rulers.delta ds.length (Windows.Dset ds s \ Windows.Dset ds s')).toNat

end Stability
