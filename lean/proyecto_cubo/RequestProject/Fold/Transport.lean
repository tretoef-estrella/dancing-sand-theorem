module

public import RequestProject.Fold.Defs
public import RequestProject.Families.Quot
public import RequestProject.LemmaW.Basic

/-!
# `C38_the_fold_in_the_group_ring.md`: Part L — (L3) transport and (L4) direct sums

Encodings:
* An isomorphism is a C20 `Doubling.Iso`; its linear equivalence is C32's `Families.isoEquiv u`
  (underlying map `u.hom.toLin`). "Weight-preserving" is C25's `LemmaW.IsWtPres`.
* "`φ` intertwines `T` with `T'`" is `φ ∘ₗ T = T' ∘ₗ φ`.
* (L4) The equivalence `dsumMapEquiv f l : ((dsumList (l.map f)).ι → A) ≃ₗ[A]
  Π_{j : Fin l.length} (f (l.get j)).ι → A` is built by recursion on the list exactly as the
  equivalence of C32 (Q1) (`LinearEquiv.sumArrowLequivProdArrow`, `Fin.consLinearEquiv`); C32
  only states its existence (with `Fd 1` and `H`), so it is rebuilt here as a definition, in
  order to show that it also carries every `Fd r` and every diagonal operator (`H`, `signOp`)
  componentwise.  "Componentwise" is `Θ (T x) = fun j => T_j (Θ x j)`.
-/

@[expose] public section

noncomputable section

namespace Fold

open DPLattice Doubling LemmaW Families Lemma35 Cocycle Step36 Finset

variable {A : Type*} [CommRing A]

/-! ### Generic transport of quotients -/

section generic

variable {X Y : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]

lemma map_range_of_comm (Φ : X ≃ₗ[A] Y) {T : Module.End A X} {S : Module.End A Y}
    (h : Φ.toLinearMap ∘ₗ T = S ∘ₗ Φ.toLinearMap) :
    (LinearMap.range T).map Φ.toLinearMap = LinearMap.range S := by
  rw [← LinearMap.range_comp, h, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]

lemma comm_sub_one (Φ : X ≃ₗ[A] Y) {T : Module.End A X} {S : Module.End A Y}
    (h : Φ.toLinearMap ∘ₗ T = S ∘ₗ Φ.toLinearMap) :
    Φ.toLinearMap ∘ₗ (T - 1) = (S - 1) ∘ₗ Φ.toLinearMap := by
  refine LinearMap.ext fun x => ?_
  have := LinearMap.congr_fun h x
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub] at this ⊢
  rw [this]

/-- (L3, L4, auxiliary) an equivalence intertwining `T₁, T₂` with `S₁, S₂` induces
`X ⧸ (range T₁ ⊔ range T₂) ≃ Y ⧸ (range S₁ ⊔ range S₂)`. -/
def quotTransport (Φ : X ≃ₗ[A] Y) {T₁ T₂ : Module.End A X} {S₁ S₂ : Module.End A Y}
    (h₁ : Φ.toLinearMap ∘ₗ T₁ = S₁ ∘ₗ Φ.toLinearMap)
    (h₂ : Φ.toLinearMap ∘ₗ T₂ = S₂ ∘ₗ Φ.toLinearMap) :
    (X ⧸ (LinearMap.range T₁ ⊔ LinearMap.range T₂)) ≃ₗ[A]
      (Y ⧸ (LinearMap.range S₁ ⊔ LinearMap.range S₂)) :=
  Submodule.Quotient.equiv _ _ Φ (by
    rw [Submodule.map_sup, map_range_of_comm Φ h₁, map_range_of_comm Φ h₂])

end generic

/-! ### (L3) -/

lemma signOp_single (M : DPLattice A) (c : ℤ) (i : M.ι) :
    signOp M c (Pi.single i 1) =
      ((-1 : A) ^ ((c - M.wt i) / 2).natAbs) • (Pi.single i 1 : M.ι → A) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [signOp_apply]
  · simp [signOp_apply, hk]

/-- (L3) a weight-preserving map intertwines `signOp M c` with `signOp N c`. -/
lemma comm_signOp {M N : DPLattice A} {φ : (M.ι → A) →ₗ[A] (N.ι → A)} (hφ : IsWtPres φ)
    (c : ℤ) : φ ∘ₗ signOp M c = signOp N c ∘ₗ φ := by
  refine ext_single fun i => funext fun j => ?_
  simp only [LinearMap.comp_apply, signOp_single, map_smul, Pi.smul_apply, smul_eq_mul,
    signOp_apply]
  by_cases h : M.wt i = N.wt j
  · rw [h]
  · rw [hφ i j h]; simp

/-- (L3) a morphism intertwines `expF M B` with `expF N B`. -/
lemma comm_expF {M N : DPLattice A} (f : Hom M N) (B : ℕ) :
    f.toLin ∘ₗ expF M B = expF N B ∘ₗ f.toLin := by
  refine LinearMap.ext fun x => ?_
  simp only [expF, LinearMap.comp_apply, LinearMap.coe_sum, Finset.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun r _ => LinearMap.congr_fun (f.comm_F r) x

/-- (L3) a morphism intertwines `tauOp M c` with `tauOp N c`. -/
lemma comm_tauOp {M N : DPLattice A} (f : Hom M N) (c : ℤ) :
    f.toLin ∘ₗ tauOp M c = tauOp N c ∘ₗ f.toLin := by
  refine LinearMap.ext fun x => ?_
  simp only [tauOp, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply, map_sub, map_add, map_smul]
  have h1 : f.toLin (M.Fd 1 x) = N.Fd 1 (f.toLin x) := LinearMap.congr_fun (f.comm_F 1) x
  have h2 : f.toLin (H M x) = H N (f.toLin x) := LinearMap.congr_fun f.comm_H x
  rw [h1, h2]

/-- (L3) a weight-preserving morphism intertwines `aOp M c B` with `aOp N c B`. -/
lemma comm_aOp {M N : DPLattice A} (f : Hom M N) (hf : IsWtPres f.toLin) (c : ℤ) (B : ℕ) :
    f.toLin ∘ₗ aOp M c B = aOp N c B ∘ₗ f.toLin := by
  rw [aOp, aOp, ← LinearMap.comp_assoc, comm_signOp hf, LinearMap.comp_assoc, comm_expF,
    LinearMap.comp_assoc]

/-- **(L3)** of `C38_the_fold_in_the_group_ring.md` (explicit equivalence): for an isomorphism
`u : Doubling.Iso M N` whose map `u.hom.toLin` is weight-preserving,
`Xbar M c B ≃ₗ[A] Xbar N c B`, induced by `u.hom.toLin`. -/
def L3equiv {M N : DPLattice A} (u : Doubling.Iso M N) (hhom : IsWtPres u.hom.toLin) (c : ℤ)
    (B : ℕ) : Xbar M c B ≃ₗ[A] Xbar N c B :=
  quotTransport (isoEquiv u) (comm_tauOp u.hom c)
    (comm_sub_one (isoEquiv u) (comm_aOp u.hom hhom c B))

/-- **(L3)** of `C38_the_fold_in_the_group_ring.md` (transport): let `u : Doubling.Iso M N` with
`IsWtPres u.hom.toLin` and `IsWtPres u.inv.toLin`. Then `u.hom.toLin` intertwines `expF M B` with
`expF N B`, `signOp M c` with `signOp N c`, `aOp M c B` with `aOp N c B`, and `tauOp M c` with
`tauOp N c`; hence `Xbar M c B ≃ₗ[A] Xbar N c B`.
The hypothesis `IsWtPres u.inv.toLin` is kept as in the file but is not used: only the map
`u.hom.toLin` is needed (and `expF`, `tauOp` need no weight hypothesis at all). -/
theorem L3 {M N : DPLattice A} (u : Doubling.Iso M N) (hhom : IsWtPres u.hom.toLin)
    (_hinv : IsWtPres u.inv.toLin) (c : ℤ) (B : ℕ) :
    u.hom.toLin ∘ₗ expF M B = expF N B ∘ₗ u.hom.toLin ∧
    u.hom.toLin ∘ₗ signOp M c = signOp N c ∘ₗ u.hom.toLin ∧
    u.hom.toLin ∘ₗ aOp M c B = aOp N c B ∘ₗ u.hom.toLin ∧
    u.hom.toLin ∘ₗ tauOp M c = tauOp N c ∘ₗ u.hom.toLin ∧
    Nonempty (Xbar M c B ≃ₗ[A] Xbar N c B) :=
  ⟨comm_expF u.hom B, comm_signOp hhom c, comm_aOp u.hom hhom c B, comm_tauOp u.hom c,
    ⟨L3equiv u hhom c B⟩⟩

/-- **(L3)** of `C38_the_fold_in_the_group_ring.md`, last sentence: over a domain of
characteristic zero the weight hypotheses hold for every isomorphism (C25 `P1`), so
`Xbar M c B ≃ₗ[A] Xbar N c B` for every `u : Doubling.Iso M N`. -/
theorem L3_charZero [IsDomain A] [CharZero A] {M N : DPLattice A} (u : Doubling.Iso M N)
    (c : ℤ) (B : ℕ) :
    IsWtPres u.hom.toLin ∧ IsWtPres u.inv.toLin ∧ Nonempty (Xbar M c B ≃ₗ[A] Xbar N c B) :=
  ⟨P1 u.hom, P1 u.inv, ⟨L3equiv u (P1 u.hom) c B⟩⟩

/-! ### (L4) -/

/-- (L4) the equivalence `((dsumList (l.map f)).ι → A) ≃ₗ[A] Π_j (f (l.get j)).ι → A`, built by
recursion on the list as in C32 (Q1). -/
def dsumMapEquiv {α : Type*} (f : α → DPLattice A) : (l : List α) →
    (((dsumList (l.map f)).ι → A) ≃ₗ[A] ((j : Fin l.length) → (f (l.get j)).ι → A))
  | [] =>
    haveI : Subsingleton ((dsumList (([] : List α).map f)).ι → A) :=
      inferInstanceAs (Subsingleton (Empty → A))
    haveI : Subsingleton ((j : Fin ([] : List α).length) → (f (([] : List α).get j)).ι → A) :=
      ⟨fun _ _ => funext fun j => j.elim0⟩
    LinearEquiv.ofSubsingleton _ _
  | a :: l =>
    (LinearEquiv.sumArrowLequivProdArrow _ _ A A).trans
      ((LinearEquiv.prodCongr (LinearEquiv.refl A _) (dsumMapEquiv f l)).trans
        (Fin.consLinearEquiv A (fun j : Fin (l.length + 1) => (f ((a :: l).get j)).ι → A)))

/-- (L4) `dsumMapEquiv` carries every `F^{(r)}` componentwise. -/
lemma dsumMapEquiv_Fd {α : Type*} (f : α → DPLattice A) (l : List α) (r : ℕ)
    (x : (dsumList (l.map f)).ι → A) :
    dsumMapEquiv f l ((dsumList (l.map f)).Fd r x) =
      fun j => (f (l.get j)).Fd r (dsumMapEquiv f l x j) := by
  induction l with
  | nil => funext j; exact j.elim0
  | cons a l ih =>
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · exact congrFun (ih (x ∘ Sum.inr)) j

/-- (L4) `dsumMapEquiv` carries every diagonal operator `x ↦ (i ↦ w (wt i) * x i)`
componentwise. -/
lemma dsumMapEquiv_diag {α : Type*} (f : α → DPLattice A) (l : List α) (w : ℤ → A)
    (x : (dsumList (l.map f)).ι → A) :
    dsumMapEquiv f l (fun i => w ((dsumList (l.map f)).wt i) * x i) =
      fun j k => w ((f (l.get j)).wt k) * dsumMapEquiv f l x j k := by
  induction l with
  | nil => funext j; exact j.elim0
  | cons a l ih =>
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · exact congrFun (ih (x ∘ Sum.inr)) j

section L4

variable {α : Type*} (f : α → DPLattice A) (l : List α)

lemma dsumMapEquiv_H (x : (dsumList (l.map f)).ι → A) :
    dsumMapEquiv f l (H (dsumList (l.map f)) x) =
      fun j => H (f (l.get j)) (dsumMapEquiv f l x j) :=
  dsumMapEquiv_diag f l (fun w => (w : A)) x

lemma dsumMapEquiv_signOp (c : ℤ) (x : (dsumList (l.map f)).ι → A) :
    dsumMapEquiv f l (signOp (dsumList (l.map f)) c x) =
      fun j => signOp (f (l.get j)) c (dsumMapEquiv f l x j) :=
  dsumMapEquiv_diag f l (fun w => (-1 : A) ^ ((c - w) / 2).natAbs) x

lemma dsumMapEquiv_expF (B : ℕ) (x : (dsumList (l.map f)).ι → A) :
    dsumMapEquiv f l (expF (dsumList (l.map f)) B x) =
      fun j => expF (f (l.get j)) B (dsumMapEquiv f l x j) := by
  simp only [expF, LinearMap.coe_sum, Finset.sum_apply, map_sum, dsumMapEquiv_Fd]
  funext j
  simp [Finset.sum_apply]

lemma dsumMapEquiv_aOp (c : ℤ) (B : ℕ) (x : (dsumList (l.map f)).ι → A) :
    dsumMapEquiv f l (aOp (dsumList (l.map f)) c B x) =
      fun j => aOp (f (l.get j)) c B (dsumMapEquiv f l x j) := by
  simp only [aOp, LinearMap.comp_apply, dsumMapEquiv_signOp, dsumMapEquiv_expF]

lemma dsumMapEquiv_tauOp (c : ℤ) (x : (dsumList (l.map f)).ι → A) :
    dsumMapEquiv f l (tauOp (dsumList (l.map f)) c x) =
      fun j => tauOp (f (l.get j)) c (dsumMapEquiv f l x j) := by
  simp only [tauOp, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_add, map_smul, dsumMapEquiv_Fd, dsumMapEquiv_H]
  rfl

/-- (L4, auxiliary) the componentwise operator `Π_j T_j` on `Π_j X_j`. -/
def piOp {J : Type*} {X : J → Type*} [∀ j, AddCommGroup (X j)] [∀ j, Module A (X j)]
    (T : ∀ j, Module.End A (X j)) : Module.End A ((j : J) → X j) :=
  LinearMap.pi fun j => T j ∘ₗ LinearMap.proj j

lemma pi_sup_pi {J : Type*} {X : J → Type*} [∀ j, AddCommGroup (X j)] [∀ j, Module A (X j)]
    (p q : ∀ j, Submodule A (X j)) :
    Submodule.pi Set.univ p ⊔ Submodule.pi Set.univ q = Submodule.pi Set.univ (fun j => p j ⊔ q j) := by
  apply le_antisymm
  · exact sup_le (Submodule.pi_mono fun j _ => le_sup_left)
      (Submodule.pi_mono fun j _ => le_sup_right)
  · intro y hy
    simp only [Submodule.mem_pi, Set.mem_univ, true_implies] at hy
    choose a ha b hb hab using fun j => Submodule.mem_sup.1 (hy j)
    refine Submodule.mem_sup.2 ⟨a, ?_, b, ?_, funext fun j => hab j⟩
    · simpa [Submodule.mem_pi] using ha
    · simpa [Submodule.mem_pi] using hb

lemma range_piOp {J : Type*} {X : J → Type*} [∀ j, AddCommGroup (X j)] [∀ j, Module A (X j)]
    (T : ∀ j, Module.End A (X j)) :
    LinearMap.range (piOp T) = Submodule.pi Set.univ fun j => LinearMap.range (T j) :=
  range_pi_eq T

/-- **(L4)** of `C38_the_fold_in_the_group_ring.md`, for a list `l.map f` (explicit equivalence):
`Xbar (dsumList (l.map f)) c B ≃ₗ[A] Π_j Xbar (f (l.get j)) c B`. -/
def L4equiv (c : ℤ) (B : ℕ) :
    Xbar (dsumList (l.map f)) c B ≃ₗ[A] ((j : Fin l.length) → Xbar (f (l.get j)) c B) :=
  (quotTransport (dsumMapEquiv f l)
      (S₁ := piOp fun j => tauOp (f (l.get j)) c)
      (S₂ := piOp fun j => aOp (f (l.get j)) c B - 1)
      (LinearMap.ext fun x => dsumMapEquiv_tauOp f l c x)
      (LinearMap.ext fun x => by
        funext j
        simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub,
          LinearEquiv.coe_coe, dsumMapEquiv_aOp, piOp, LinearMap.pi_apply,
          LinearMap.proj_apply, Pi.sub_apply])).trans
    ((Submodule.quotEquivOfEq _ _ (by rw [range_piOp, range_piOp, pi_sup_pi])).trans
      (Submodule.quotientPi _))

/-- **(L4)** of `C38_the_fold_in_the_group_ring.md`, general form for a list `l.map f`: the
equivalence `Θ : ((dsumList (l.map f)).ι → A) ≃ₗ[A] Π_{j : Fin l.length} (f (l.get j)).ι → A`
(built as in C32 (Q1)) carries `Fd r` (every `r`), `H`, `signOp`, `expF`, `aOp`, `tauOp`
componentwise; hence `Xbar (dsumList (l.map f)) c B ≃ₗ[A] Π_j Xbar (f (l.get j)) c B`. -/
theorem L4_map (c : ℤ) (B : ℕ) :
    ∃ Θ : ((dsumList (l.map f)).ι → A) ≃ₗ[A] ((j : Fin l.length) → (f (l.get j)).ι → A),
      (∀ r x, Θ ((dsumList (l.map f)).Fd r x) = fun j => (f (l.get j)).Fd r (Θ x j)) ∧
      (∀ x, Θ (H (dsumList (l.map f)) x) = fun j => H (f (l.get j)) (Θ x j)) ∧
      (∀ x, Θ (signOp (dsumList (l.map f)) c x) = fun j => signOp (f (l.get j)) c (Θ x j)) ∧
      (∀ x, Θ (expF (dsumList (l.map f)) B x) = fun j => expF (f (l.get j)) B (Θ x j)) ∧
      (∀ x, Θ (aOp (dsumList (l.map f)) c B x) = fun j => aOp (f (l.get j)) c B (Θ x j)) ∧
      (∀ x, Θ (tauOp (dsumList (l.map f)) c x) = fun j => tauOp (f (l.get j)) c (Θ x j)) ∧
      Nonempty (Xbar (dsumList (l.map f)) c B ≃ₗ[A] ((j : Fin l.length) → Xbar (f (l.get j)) c B)) :=
  ⟨dsumMapEquiv f l, dsumMapEquiv_Fd f l, dsumMapEquiv_H f l, dsumMapEquiv_signOp f l c,
    dsumMapEquiv_expF f l B, dsumMapEquiv_aOp f l c B, dsumMapEquiv_tauOp f l c,
    ⟨L4equiv f l c B⟩⟩

end L4

/-- **(L4)** of `C38_the_fold_in_the_group_ring.md` (direct sums): for every list
`Ls : List (DPLattice A)`, the equivalence
`Θ : ((dsumList Ls).ι → A) ≃ₗ[A] Π_{j : Fin Ls.length} (Ls.get j).ι → A` (built as in C32 (Q1))
intertwines `Fd r` (every `r`), `H`, `signOp`, `expF`, `aOp`, `tauOp` componentwise; hence
`Xbar (dsumList Ls) c B ≃ₗ[A] Π_j Xbar (Ls.get j) c B`. -/
theorem L4 (Ls : List (DPLattice A)) (c : ℤ) (B : ℕ) :
    ∃ Θ : ((dsumList Ls).ι → A) ≃ₗ[A] ((j : Fin Ls.length) → (Ls.get j).ι → A),
      (∀ r x, Θ ((dsumList Ls).Fd r x) = fun j => (Ls.get j).Fd r (Θ x j)) ∧
      (∀ x, Θ (H (dsumList Ls) x) = fun j => H (Ls.get j) (Θ x j)) ∧
      (∀ x, Θ (signOp (dsumList Ls) c x) = fun j => signOp (Ls.get j) c (Θ x j)) ∧
      (∀ x, Θ (expF (dsumList Ls) B x) = fun j => expF (Ls.get j) B (Θ x j)) ∧
      (∀ x, Θ (aOp (dsumList Ls) c B x) = fun j => aOp (Ls.get j) c B (Θ x j)) ∧
      (∀ x, Θ (tauOp (dsumList Ls) c x) = fun j => tauOp (Ls.get j) c (Θ x j)) ∧
      Nonempty (Xbar (dsumList Ls) c B ≃ₗ[A] ((j : Fin Ls.length) → Xbar (Ls.get j) c B)) := by
  have h := L4_map (fun X : DPLattice A => X) Ls c B
  rw [List.map_id'] at h
  exact h

end Fold
