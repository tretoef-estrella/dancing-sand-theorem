module

public import RequestProject.Bend.Defs

/-!
# `C50d_the_bend.md`: Part B, (W) — the window

`Windows.Dset ds s ⊆ Windows.Ids ds ⊆ range ds.length`, so `Rulers.oE` of a subset is a sum of
distinct powers `2^t` with `t < k` (C3 `Rulers.oE_lt`); the splitting is C3 `Rulers.oE_sdiff`.
-/

@[expose] public section

noncomputable section

namespace Bend

/-- **(W)** of `C50d_the_bend.md` (the window): for `s s' : Fin (Dance.slots ds 1)` with
`Windows.Dset ds s' ⊆ Windows.Dset ds s`,
`oE (Dset ds s) = oE (Dset ds s') + oE (Dset ds s \ Dset ds s')` and
`oE (Dset ds s \ Dset ds s') ≤ 2 ^ ds.length − 1` (`oE = Rulers.oE`, `Dset = Windows.Dset`).
Stated for every digit list `ds` (the file has `ds = Families.ds l`): more general. -/
theorem W (ds : List Bool) (s s' : Fin (Dance.slots ds 1))
    (h : Windows.Dset ds s' ⊆ Windows.Dset ds s) :
    Rulers.oE (Windows.Dset ds s) =
        Rulers.oE (Windows.Dset ds s') + Rulers.oE (Windows.Dset ds s \ Windows.Dset ds s') ∧
      Rulers.oE (Windows.Dset ds s \ Windows.Dset ds s') ≤ 2 ^ ds.length - 1 := by
  have h1 := Rulers.oE_sdiff h
  have h2 := Rulers.oE_lt (Windows.Dset ds s \ Windows.Dset ds s') ds.length
    (fun t ht => Stability.lt_of_mem_Dset (Finset.mem_sdiff.1 ht).1)
  omega

end Bend
