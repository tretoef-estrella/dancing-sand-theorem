module

public import RequestProject.FormalDance.All

/-!
# `C45_conjugation_and_general_eta.md`: Definitions (new) — `cj` and `cjSys`

Namespace `Conjugation`. Nothing listed in the Setting of the file is redefined: `Bf` is C40's
`FormalOps.Bf` (`x.coef j f` = coefficient of `F^{(j)}` at the target floor `f`), and the
matrices are Mathlib's `Matrix n n (Bf A)` as in C40b.

* `cj u x` is the operator with `(cj u x).coef j f = u ^ j * x.coef j f` (conjugation by the
  diagonal operator `u^D`), exactly as in the file.
* `cjSys c u w G s s' = ((c * w s * (w s')⁻¹ : Aˣ) : A) • cj u (G s s')`, exactly as in the file
  (`c u : Aˣ`, `w : n → Aˣ`; `cj` is applied to the underlying element `(u : A)`).
-/

@[expose] public section

noncomputable section

namespace Conjugation

open FormalOps FormalDance Finset

variable {A : Type*} [CommRing A]

/-- Definitions (new) of `C45_conjugation_and_general_eta.md`: conjugation by the diagonal
operator `u^D`, `(cj u x).coef j f = u ^ j * x.coef j f`. -/
def cj (u : A) (x : Bf A) : Bf A := ⟨fun j f => u ^ j * x.coef j f⟩

/-- Definitions (new) of `C45_conjugation_and_general_eta.md` (simp lemma for `cj`). -/
@[simp] lemma coef_cj (u : A) (x : Bf A) (j : ℕ) (f : ℤ) :
    (cj u x).coef j f = u ^ j * x.coef j f := rfl

/-- Definitions (new) of `C45_conjugation_and_general_eta.md`: conjugation of a system,
`cjSys c u w G s s' = ((c * w s * (w s')⁻¹ : Aˣ) : A) • cj u (G s s')`. -/
def cjSys {n : Type*} (c u : Aˣ) (w : n → Aˣ) (G : Matrix n n (Bf A)) : Matrix n n (Bf A) :=
  fun s s' => ((c * w s * (w s')⁻¹ : Aˣ) : A) • cj (u : A) (G s s')

/-- Definitions (new) of `C45_conjugation_and_general_eta.md` (unfolding lemma for `cjSys`). -/
lemma cjSys_apply {n : Type*} (c u : Aˣ) (w : n → Aˣ) (G : Matrix n n (Bf A)) (s s' : n) :
    cjSys c u w G s s' = ((c * w s * (w s')⁻¹ : Aˣ) : A) • cj (u : A) (G s s') := rfl

end Conjugation
