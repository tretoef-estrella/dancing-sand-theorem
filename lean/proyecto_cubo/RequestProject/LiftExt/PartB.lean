module

public import RequestProject.LiftExt.PartX

/-!
# `C26_lifting_and_extension.md`: Part B — Lemma 3.3 for one pair, both forms, both cases

Encodings (namespace `LiftExt`), as in `Basic.lean`; moreover:

* the duality `ι` is C25's contravariant dual: `dual M` (same basis and weights,
  `F^{(r)} = trM (M.Ed r)`, `E^{(r)} = trM (M.Fd r)`), `dualHom f` (underlying map
  `trM f.toLin`), and the identity isomorphisms `isoDualDual`, `isoDualDelta`, `isoDualNabla`
  (C20 `Doubling.Iso`, underlying maps `.hom.toLin`, `.inv.toLin`, all equal to the identity);
* **lifting** (B1): every `h : Hom (delta A l) Z` factors as `Hom.comp g h'`;
* **extension** (B2): every `k : Hom Y (nabla A m)` is `Hom.comp k' f`;
* `ℤ_[2]` is Mathlib's `PadicInt 2`.
-/

@[expose] public section

noncomputable section

namespace LiftExt

open DPLattice WeylFilt Doubling LemmaW Finset

variable {A : Type*} [CommRing A]

/-! ### (B1) Lifting -/

section B1

variable {l m : ℕ} {X Z : DPLattice A} {f : Hom (nabla A m) X} {g : Hom X Z}

/-- (B1), case `m ≤ l`: (L1), since `nabla A m` has weights in `[−m, m] ⊆ [−l, l]`. -/
theorem B1_le (hml : m ≤ l) (hfg : ShortExact f g) (hf : IsWtPres f.toLin)
    (hg : IsWtPres g.toLin) (h : Hom (delta A l) Z) (hh : IsWtPres h.toLin) :
    ∃ h' : Hom (delta A l) X, Hom.comp g h' = h := by
  obtain ⟨-, -, -, h', -, hh'⟩ :=
    L1 l hfg hf hg ((wtIn_nabla m).mono (by omega) (by omega)) h hh
  exact ⟨h', hh'⟩

/-- (B1), case `m > l`: by (D5), (D4) the sequence `dual Z → dual X → delta A m` (maps
`dualHom g` and `(isoDualNabla m).hom ∘ dualHom f`) is short exact and weight-preserving;
`k := (isoDualDelta l).hom ∘ dualHom h` is weight-preserving and `nabla A l` has weights in
`[−l, l] ⊆ [−m, m]`, so (X1) gives `k'` with `k' ∘ dualHom g = k`; then
`h' := (isoDualDual X).hom ∘ dualHom k' ∘ (isoDualNabla l).inv` satisfies `g ∘ h' = h`. -/
theorem B1_gt (hml : l < m) (hfg : ShortExact f g) (hf : IsWtPres f.toLin)
    (hg : IsWtPres g.toLin) (h : Hom (delta A l) Z) (hh : IsWtPres h.toLin) :
    ∃ h' : Hom (delta A l) X, Hom.comp g h' = h := by
  have hD := D5 hfg
  let g' : Hom (dual X) (delta A m) := Hom.comp (isoDualNabla m).hom (dualHom f)
  have e2 : g'.toLin = trM f.toLin := LinearMap.id_comp _
  have hD' : ShortExact (dualHom g) g' := by
    refine ⟨hD.inj, ?_, ?_⟩
    · rw [e2]; exact hD.surj
    · rw [e2]; exact hD.exact
  have hg' : IsWtPres g'.toLin := fun i j hij => by
    rw [e2]; exact dualHom_wtPres hf i j hij
  let k : Hom (dual Z) (nabla A l) := Hom.comp (isoDualDelta l).hom (dualHom h)
  have ek : k.toLin = trM h.toLin := LinearMap.id_comp _
  have hk : IsWtPres k.toLin := fun i j hij => by
    rw [ek]; exact dualHom_wtPres hh i j hij
  obtain ⟨k', hk', -⟩ := X1 m hD' (dualHom_wtPres hg) hg'
    ((wtIn_nabla l).mono (by omega) (by omega)) k hk
  have t1 : k'.toLin ∘ₗ trM g.toLin = trM h.toLin := by
    rw [← ek]; exact congrArg Hom.toLin hk'
  have t2 : g.toLin ∘ₗ trM k'.toLin = h.toLin := by
    have := congrArg trM t1
    rwa [trM_comp, trM_trM, trM_trM] at this
  refine ⟨Hom.comp (isoDualDual X).hom (Hom.comp (dualHom k') (isoDualNabla l).inv),
    Hom.ext' ?_⟩
  change g.toLin ∘ₗ (LinearMap.id ∘ₗ (trM k'.toLin ∘ₗ LinearMap.id)) = h.toLin
  rw [LinearMap.id_comp, LinearMap.comp_id, t2]

end B1

/-- (B1) **Lifting.** For all `l m : ℕ`: if `f : Hom (nabla A m) X`, `g : Hom X Z` is short
exact with `f.toLin`, `g.toLin` weight-preserving, then every `h : Hom (delta A l) Z` with
`h.toLin` weight-preserving lifts: `∃ h' : Hom (delta A l) X, Hom.comp g h' = h`. -/
theorem B1 (l m : ℕ) {X Z : DPLattice A} {f : Hom (nabla A m) X} {g : Hom X Z}
    (hfg : ShortExact f g) (hf : IsWtPres f.toLin) (hg : IsWtPres g.toLin)
    (h : Hom (delta A l) Z) (hh : IsWtPres h.toLin) :
    ∃ h' : Hom (delta A l) X, Hom.comp g h' = h := by
  rcases le_or_gt m l with hml | hml
  · exact B1_le hml hfg hf hg h hh
  · exact B1_gt hml hfg hf hg h hh

/-! ### (B2) Extension -/

section B2

variable {l m : ℕ} {Y X : DPLattice A} {f : Hom Y X} {g : Hom X (delta A l)}

/-- (B2), case `m ≤ l`: (X1), since `nabla A m` has weights in `[−m, m] ⊆ [−l, l]`. -/
theorem B2_le (hml : m ≤ l) (hfg : ShortExact f g) (hf : IsWtPres f.toLin)
    (hg : IsWtPres g.toLin) (k : Hom Y (nabla A m)) (hk : IsWtPres k.toLin) :
    ∃ k' : Hom X (nabla A m), Hom.comp k' f = k := by
  obtain ⟨k', hk', -⟩ := X1 l hfg hf hg ((wtIn_nabla m).mono (by omega) (by omega)) k hk
  exact ⟨k', hk'⟩

/-- (B2), case `m > l`: by (D5), (D4) the sequence `nabla A l → dual X → dual Y` (maps
`dualHom g ∘ (isoDualDelta l).inv` and `dualHom f`) is short exact and weight-preserving;
`h := dualHom k ∘ (isoDualNabla m).inv` is weight-preserving and the kernel `nabla A l` has
weights in `[−l, l] ⊆ [−m, m]`, so (L1) gives `h'` with `dualHom f ∘ h' = h`; then
`k' := (isoDualDelta m).hom ∘ dualHom h' ∘ (isoDualDual X).inv` satisfies `k' ∘ f = k`. -/
theorem B2_gt (hml : l < m) (hfg : ShortExact f g) (hf : IsWtPres f.toLin)
    (hg : IsWtPres g.toLin) (k : Hom Y (nabla A m)) (hk : IsWtPres k.toLin) :
    ∃ k' : Hom X (nabla A m), Hom.comp k' f = k := by
  have hD := D5 hfg
  let f' : Hom (nabla A l) (dual X) := Hom.comp (dualHom g) (isoDualDelta l).inv
  have e1 : f'.toLin = trM g.toLin := LinearMap.comp_id _
  have hD' : ShortExact f' (dualHom f) := by
    refine ⟨?_, hD.surj, ?_⟩
    · rw [e1]; exact hD.inj
    · rw [e1]; exact hD.exact
  have hf' : IsWtPres f'.toLin := fun i j hij => by
    rw [e1]; exact dualHom_wtPres hg i j hij
  let h : Hom (delta A m) (dual Y) := Hom.comp (dualHom k) (isoDualNabla m).inv
  have eh : h.toLin = trM k.toLin := LinearMap.comp_id _
  have hh : IsWtPres h.toLin := fun i j hij => by
    rw [eh]; exact dualHom_wtPres hk i j hij
  obtain ⟨-, -, -, h', -, hh'⟩ := L1 m hD' hf' (dualHom_wtPres hf)
    ((wtIn_nabla l).mono (by omega) (by omega)) h hh
  have t1 : trM f.toLin ∘ₗ h'.toLin = trM k.toLin := by
    rw [← eh]; exact congrArg Hom.toLin hh'
  have t2 : trM h'.toLin ∘ₗ f.toLin = k.toLin := by
    have := congrArg trM t1
    rwa [trM_comp, trM_trM, trM_trM] at this
  refine ⟨Hom.comp (isoDualDelta m).hom (Hom.comp (dualHom h') (isoDualDual X).inv),
    Hom.ext' ?_⟩
  change (LinearMap.id ∘ₗ (trM h'.toLin ∘ₗ LinearMap.id)) ∘ₗ f.toLin = k.toLin
  rw [LinearMap.id_comp, LinearMap.comp_id, t2]

end B2

/-- (B2) **Extension.** For all `l m : ℕ`: if `f : Hom Y X`, `g : Hom X (delta A l)` is short
exact with `f.toLin`, `g.toLin` weight-preserving, then every `k : Hom Y (nabla A m)` with
`k.toLin` weight-preserving extends: `∃ k' : Hom X (nabla A m), Hom.comp k' f = k`. -/
theorem B2 (l m : ℕ) {Y X : DPLattice A} {f : Hom Y X} {g : Hom X (delta A l)}
    (hfg : ShortExact f g) (hf : IsWtPres f.toLin) (hg : IsWtPres g.toLin)
    (k : Hom Y (nabla A m)) (hk : IsWtPres k.toLin) :
    ∃ k' : Hom X (nabla A m), Hom.comp k' f = k := by
  rcases le_or_gt m l with hml | hml
  · exact B2_le hml hfg hf hg k hk
  · exact B2_gt hml hfg hf hg k hk

/-! ### (B3), (B4) -/

/-- (B3), lifting: over a domain of characteristic zero, (B1) holds without the
weight-preservation hypotheses (they follow from C25 (P1)). -/
theorem B3_lift [IsDomain A] [CharZero A] (l m : ℕ) {X Z : DPLattice A}
    {f : Hom (nabla A m) X} {g : Hom X Z} (hfg : ShortExact f g) (h : Hom (delta A l) Z) :
    ∃ h' : Hom (delta A l) X, Hom.comp g h' = h :=
  B1 l m hfg (P1 f) (P1 g) h (P1 h)

/-- (B3), extension: over a domain of characteristic zero, (B2) holds without the
weight-preservation hypotheses (they follow from C25 (P1)). -/
theorem B3_ext [IsDomain A] [CharZero A] (l m : ℕ) {Y X : DPLattice A}
    {f : Hom Y X} {g : Hom X (delta A l)} (hfg : ShortExact f g) (k : Hom Y (nabla A m)) :
    ∃ k' : Hom X (nabla A m), Hom.comp k' f = k :=
  B2 l m hfg (P1 f) (P1 g) k (P1 k)

/-- (B3) Both forms together: over a domain of characteristic zero, (B1) and (B2) hold without
the weight-preservation hypotheses. -/
theorem B3 [IsDomain A] [CharZero A] (l m : ℕ) :
    (∀ {X Z : DPLattice A} {f : Hom (nabla A m) X} {g : Hom X Z}, ShortExact f g →
      ∀ h : Hom (delta A l) Z, ∃ h' : Hom (delta A l) X, Hom.comp g h' = h) ∧
    (∀ {Y X : DPLattice A} {f : Hom Y X} {g : Hom X (delta A l)}, ShortExact f g →
      ∀ k : Hom Y (nabla A m), ∃ k' : Hom X (nabla A m), Hom.comp k' f = k) :=
  ⟨fun hfg h => B3_lift l m hfg h, fun hfg k => B3_ext l m hfg k⟩

/-- (B4) **The case of the paper**: (B1) and (B2) for `A = ℤ_[2]`, all `l m : ℕ`, with no
weight hypotheses. -/
theorem B4 (l m : ℕ) :
    (∀ {X Z : DPLattice ℤ_[2]} {f : Hom (nabla ℤ_[2] m) X} {g : Hom X Z}, ShortExact f g →
      ∀ h : Hom (delta ℤ_[2] l) Z, ∃ h' : Hom (delta ℤ_[2] l) X, Hom.comp g h' = h) ∧
    (∀ {Y X : DPLattice ℤ_[2]} {f : Hom Y X} {g : Hom X (delta ℤ_[2] l)}, ShortExact f g →
      ∀ k : Hom Y (nabla ℤ_[2] m), ∃ k' : Hom X (nabla ℤ_[2] m), Hom.comp k' f = k) :=
  B3 l m

/-! ### (B5) -/

/-- (B5) **Consistency with C25.** For a short exact sequence `f : Hom (nabla A m) X`,
`g : Hom X (delta A l)` with `f.toLin`, `g.toLin` weight-preserving, (B1) with `Z = delta A l`,
`h = Hom.id` gives a section of `g`, and (B2) with `Y = nabla A m`, `k = Hom.id` gives a
retraction of `f`: this is exactly the conclusion of C25 (E2), obtained here from (B1), (B2). -/
theorem B5 (l m : ℕ) {X : DPLattice A} {f : Hom (nabla A m) X} {g : Hom X (delta A l)}
    (hfg : ShortExact f g) (hf : IsWtPres f.toLin) (hg : IsWtPres g.toLin) :
    (∃ s : Hom (delta A l) X, Hom.comp g s = Hom.id _) ∧
    (∃ r : Hom X (nabla A m), Hom.comp r f = Hom.id _) :=
  ⟨B1 l m hfg hf hg (Hom.id _) (isWtPres_id _), B2 l m hfg hf hg (Hom.id _) (isWtPres_id _)⟩

end LiftExt
