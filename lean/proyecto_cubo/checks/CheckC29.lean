import RequestProject.Filt.All

/-! Auditor's check file for Lean piece C29 (Grepy Escribano, 8 Oct 2026).
Restated by hand from `C29_filtrations_and_dance_lattices.md`, with «weight-preserving» written
out entrywise instead of `IsWtPres`: (S1), (S2) with the operators written out and the
morphisms commuting; (I1); (E1), (E2) with the weight conditions written out; (E3); (V1), (V2);
(T0) the five defining equations; (T1), (T2), (T3); (Z1); then `#print axioms`. -/

open DPLattice WeylFilt Doubling LemmaW Cocycle Filt

section hand
variable {A : Type} [CommRing A]

-- (S1) the sub-lattice: basis κ, weights wK, operators p ∘ X.Fd r ∘ j, and j commutes.
example (X : DPLattice A) {κ : Type} [Fintype κ] [DecidableEq κ] (wK : κ → ℤ)
    (j : (κ → A) →ₗ[A] (X.ι → A)) (p : (X.ι → A) →ₗ[A] (κ → A))
    (hpj : p ∘ₗ j = LinearMap.id)
    (hj : ∀ k i, wK k ≠ X.wt i → j (Pi.single k 1) i = 0)
    (hp : ∀ i k, X.wt i ≠ wK k → p (Pi.single i 1) k = 0)
    (hF : ∀ r x, X.Fd r (j x) ∈ LinearMap.range j)
    (hE : ∀ r x, X.Ed r (j x) ∈ LinearMap.range j) :
    (∀ k, (sub X wK j p hpj hj hp hF hE).wt k = wK k) ∧
    (∀ r x, (sub X wK j p hpj hj hp hF hE).Fd r x = p (X.Fd r (j x))) ∧
    (∀ r x, (sub X wK j p hpj hj hp hF hE).Ed r x = p (X.Ed r (j x))) ∧
    (subHom X wK j p hpj hj hp hF hE).toLin = j ∧
    (∀ r x, j (p (X.Fd r (j x))) = X.Fd r (j x)) := by
  refine ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, fun r x => ?_⟩
  have := LinearMap.congr_fun ((subHom X wK j p hpj hj hp hF hE).comm_F r) x
  exact this

-- (S2) the quotient lattice: operators q ∘ X.Fd r ∘ s, and q commutes.
example (X : DPLattice A) {κ : Type} [Fintype κ] [DecidableEq κ] (wK : κ → ℤ)
    (q : (X.ι → A) →ₗ[A] (κ → A)) (s : (κ → A) →ₗ[A] (X.ι → A))
    (hqs : q ∘ₗ s = LinearMap.id)
    (hq : ∀ i k, X.wt i ≠ wK k → q (Pi.single i 1) k = 0)
    (hs : ∀ k i, wK k ≠ X.wt i → s (Pi.single k 1) i = 0)
    (hF : ∀ r x, x ∈ LinearMap.ker q → X.Fd r x ∈ LinearMap.ker q)
    (hE : ∀ r x, x ∈ LinearMap.ker q → X.Ed r x ∈ LinearMap.ker q) :
    (∀ k, (quot X wK q s hqs hq hs hF hE).wt k = wK k) ∧
    (∀ r x, (quot X wK q s hqs hq hs hF hE).Fd r x = q (X.Fd r (s x))) ∧
    (quotHom X wK q s hqs hq hs hF hE).toLin = q ∧
    (∀ r x, q (X.Fd r x) = q (X.Fd r (s (q x)))) := by
  refine ⟨fun _ => rfl, fun _ _ => rfl, rfl, fun r x => ?_⟩
  have := LinearMap.congr_fun ((quotHom X wK q s hqs hq hs hF hE).comm_F r) x
  exact this

variable {M' M Q N' N N'' X Y : DPLattice A}

-- (I1) with both maps of the isomorphism weight-preserving, written out.
example (e : Doubling.Iso X Y)
    (he : ∀ i j, X.wt i ≠ Y.wt j → e.hom.toLin (Pi.single i 1) j = 0)
    (he' : ∀ i j, Y.wt i ≠ X.wt j → e.inv.toLin (Pi.single i 1) j = 0) :
    (HasDeltaFilt X → HasDeltaFilt Y) ∧ (HasNablaFilt X → HasNablaFilt Y) :=
  I1 e he he'

-- (E1) extensions of Δ-filtered lattices, weights written out.
example (f : Hom M' M) (g : Hom M Q) (h : ShortExact f g)
    (hf : ∀ i j, M'.wt i ≠ M.wt j → f.toLin (Pi.single i 1) j = 0)
    (hg : ∀ i j, M.wt i ≠ Q.wt j → g.toLin (Pi.single i 1) j = 0)
    (hM' : HasDeltaFilt M') (hQ : HasDeltaFilt Q) : HasDeltaFilt M :=
  E1 f g h hf hg hM' hQ

-- (E2) extensions of ∇-filtered lattices, weights written out.
example (f : Hom N' N) (g : Hom N N'') (h : ShortExact f g)
    (hf : ∀ i j, N'.wt i ≠ N.wt j → f.toLin (Pi.single i 1) j = 0)
    (hg : ∀ i j, N.wt i ≠ N''.wt j → g.toLin (Pi.single i 1) j = 0)
    (hN' : HasNablaFilt N') (hN'' : HasNablaFilt N'') : HasNablaFilt N :=
  E2 f g h hf hg hN' hN''

-- (E3) direct sums, both filtrations.
example (hMd : HasDeltaFilt M) (hNd : HasDeltaFilt N) (hMn : HasNablaFilt M)
    (hNn : HasNablaFilt N) :
    HasDeltaFilt (Lemma35.dsum M N) ∧ HasNablaFilt (Lemma35.dsum M N) :=
  ⟨E3.1 hMd hNd, E3.2 hMn hNn⟩

-- (V1) [char 0] and (V2) [Φ].
example [IsDomain A] [CharZero A] (hM : HasDeltaFilt M) (hN : HasNablaFilt N) :
    HasDeltaFilt (tensorV M) ∧ HasNablaFilt (tensorV N) :=
  ⟨V1_delta hM, V1_nabla hN⟩
example [IsDomain A] [CharZero A] [OddUnits A] (hM : HasDeltaFilt M) (hN : HasNablaFilt N) :
    HasDeltaFilt (phi M) ∧ HasNablaFilt (phi N) :=
  ⟨V2_delta hM, V2_nabla hN⟩

-- (T0) the defining equations.
example [IsDomain A] [CharZero A] [OddUnits A] (l n : ℕ) :
    Filt.T A 0 = one A ∧ Filt.T A (2 * l + 1) = phi (Filt.T A l) ∧
    Filt.T A (2 * l + 2) = tensorV (phi (Filt.T A l)) ∧ tpow A 0 = one A ∧
    tpow A (n + 1) = tensorV (tpow A n) :=
  ⟨T_zero A, T_odd A l, T_even A l, tpow_zero A, tpow_succ A n⟩

-- (T1), (T2), (T3).
example [IsDomain A] [CharZero A] [OddUnits A] (l : ℕ) :
    HasDeltaFilt (Filt.T A l) ∧ HasNablaFilt (Filt.T A l) := T1 l
example [IsDomain A] [CharZero A] (n : ℕ) :
    HasDeltaFilt (tpow A n) ∧ HasNablaFilt (tpow A n) := T2 n
example [IsDomain A] [CharZero A] [OddUnits A] (hΔ : HasDeltaFilt N) (hN : HasNablaFilt N) :
    HasDeltaFilt (tensorV (tensorV (phi N))) ∧ HasNablaFilt (tensorV (tensorV (phi N))) ∧
    HasDeltaFilt (Lemma35.dsum (Lemma35.dsum (phi N) (phi N)) (phi (tensorV N))) ∧
    HasNablaFilt (Lemma35.dsum (Lemma35.dsum (phi N) (phi N)) (phi (tensorV N))) := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := T3 hΔ hN
  exact ⟨a, b, c, d⟩
end hand

-- (Z1) over ℤ_[2], and one instance: T(6) (λ + 1 = 7 = 4 + 2 + 1).
example : (∀ l, HasDeltaFilt (Filt.T ℤ_[2] l) ∧ HasNablaFilt (Filt.T ℤ_[2] l)) ∧
    (∀ n, HasDeltaFilt (tpow ℤ_[2] n) ∧ HasNablaFilt (tpow ℤ_[2] n)) :=
  ⟨Z1.1, Z1.2.1⟩
example : HasDeltaFilt (Filt.T ℤ_[2] 6) ∧ HasNablaFilt (Filt.T ℤ_[2] 6) := Z1.1 6

#print axioms Filt.S1
#print axioms Filt.S2
#print axioms Filt.I1
#print axioms Filt.I2
#print axioms Filt.E1
#print axioms Filt.E2
#print axioms Filt.E3
#print axioms Filt.V1
#print axioms Filt.V2
#print axioms Filt.T0
#print axioms Filt.T1
#print axioms Filt.T2
#print axioms Filt.T3
#print axioms Filt.T3_T
#print axioms Filt.Z1
