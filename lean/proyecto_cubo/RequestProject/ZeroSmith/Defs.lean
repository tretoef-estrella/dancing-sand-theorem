module

public import RequestProject.ContZero.All
public import RequestProject.Smith2.All

/-!
# `C49c_smith_form_and_cokernel_at_zero.md`: Definition (new) — `Data0`

Namespace `ZeroSmith`. Nothing listed in the Setting of the file is redefined: `Dset`, `Ids` and
`finalMatrix` are C14's (`Windows`), `cHatH` is C6's (`Houses`), `Dance.mCount` is C13's. The only
new definition is `Data0`, written exactly as in the file (with `N = 2 ^ Dance.mCount ds`,
`K = 2 ^ ds.length`).
-/

@[expose] public section

noncomputable section

namespace ZeroSmith

open Windows

/-- Definition (new) of `C49c_smith_form_and_cokernel_at_zero.md`: the support and the entry
valuations at `i = 0`. For all `s, s' : Fin N` (the binders are typed, since `M' s s'` needs
elements of `Fin N`): if `¬ Dset ds s' ⊆ Dset ds s` then `M' s s' = 0`; if
`Dset ds s = ∅` then `M' s s' = 0`; and if `Dset ds s' ⊆ Dset ds s` and `Dset ds s ≠ ∅` then
`M' s s' ≠ 0` and there is `n : ℕ` with
`(n : ℤ) = α 2^k + cHatH (Ids ds) k (2^k − 1) α (Dset ds s) (Dset ds s')`, `2^n ∣ M' s s'` and
`¬ 2^(n+1) ∣ M' s s'`. -/
def Data0 (ds : List Bool) (α : ℕ)
    (M' : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ) : Prop :=
  ∀ s s' : Fin (2 ^ Dance.mCount ds),
    (¬ Dset ds s' ⊆ Dset ds s → M' s s' = 0) ∧ (Dset ds s = ∅ → M' s s' = 0) ∧
    (Dset ds s' ⊆ Dset ds s → Dset ds s ≠ ∅ → M' s s' ≠ 0 ∧ ∃ n : ℕ,
      (n : ℤ) = (α : ℤ) * 2 ^ ds.length + Houses.cHatH (Ids ds) ds.length (2 ^ ds.length - 1)
        (α : ℤ) (Dset ds s) (Dset ds s') ∧ 2 ^ n ∣ M' s s' ∧ ¬ 2 ^ (n + 1) ∣ M' s s')

end ZeroSmith
