module

public import KhanSL2.CEEquivariance

@[expose] public section

/-!
# Derivations of the cochain algebra (blueprint `def:toolkit`)

* `cochain_linearMap_ext`: a linear map on cochains is determined by its value at `1` and by a
  step along left multiplication by generators.
* `IsOddDer`, `IsEvenDer`: graded derivations of the exterior product, odd ones twisted by the
  parity automorphism.
* Extensionality on generators, and closure of (anti)commutators.
-/

noncomputable section

namespace KhanSL2

/-- A linear map on cochains is determined by its value at `1` and an induction step along left
multiplication by a generator. -/
theorem cochain_linearMap_ext {X Y : Cochain →ₗ[ℂ] Cochain} (h1 : X cochainOne = Y cochainOne)
    (hstep : ∀ m u, X u = Y u → X (generator m * u) = Y (generator m * u)) : X = Y := by
  apply LinearMap.ext
  intro u
  induction u using cochain_induction with
  | hzero => simp
  | hone => exact h1
  | hadd u v hu hv => simp only [map_add, hu, hv]
  | hsmul r u hu => simp only [map_smul, hu]
  | hgen m u hu => exact hstep m u hu

/-- An odd derivation of the exterior product (twisted by the parity automorphism) that
anticommutes with parity. -/
structure IsOddDer (D : Cochain →ₗ[ℂ] Cochain) : Prop where
  mul : ∀ u v, D (u * v) = D u * v + cochainParity u * D v
  parity : ∀ u, D (cochainParity u) = -cochainParity (D u)

/-- An even derivation of the exterior product that commutes with parity. -/
structure IsEvenDer (E : Cochain →ₗ[ℂ] Cochain) : Prop where
  mul : ∀ u v, E (u * v) = E u * v + u * E v
  parity : ∀ u, E (cochainParity u) = cochainParity (E u)

theorem cochainParity_one : cochainParity cochainOne = cochainOne := by
  rw [← cochain_one_eq, map_one]

theorem IsOddDer.map_one {D : Cochain →ₗ[ℂ] Cochain} (hD : IsOddDer D) : D cochainOne = 0 := by
  have h := hD.mul 1 1
  rw [one_mul, mul_one, show cochainParity (1 : Cochain) = 1 from cochainParity.map_one, one_mul] at h
  rw [← cochain_one_eq]
  simpa using h

theorem IsEvenDer.map_one {E : Cochain →ₗ[ℂ] Cochain} (hE : IsEvenDer E) : E cochainOne = 0 := by
  have h := hE.mul 1 1
  rw [one_mul, mul_one, one_mul] at h
  rw [← cochain_one_eq]
  simpa using h

/-- Two odd derivations agreeing on generators are equal. -/
theorem IsOddDer.ext {D D' : Cochain →ₗ[ℂ] Cochain} (hD : IsOddDer D) (hD' : IsOddDer D')
    (h : ∀ m, D (generator m) = D' (generator m)) : D = D' := by
  apply cochain_linearMap_ext (by rw [hD.map_one, hD'.map_one])
  intro m u hu
  rw [hD.mul, hD'.mul, h, hu]

/-- Two even derivations agreeing on generators are equal. -/
theorem IsEvenDer.ext {E E' : Cochain →ₗ[ℂ] Cochain} (hE : IsEvenDer E) (hE' : IsEvenDer E')
    (h : ∀ m, E (generator m) = E' (generator m)) : E = E' := by
  apply cochain_linearMap_ext (by rw [hE.map_one, hE'.map_one])
  intro m u hu
  rw [hE.mul, hE'.mul, h, hu]

/-- The commutator of an odd and an even derivation is odd. -/
theorem IsOddDer.commutator {D E : Cochain →ₗ[ℂ] Cochain} (hD : IsOddDer D) (hE : IsEvenDer E) :
    IsOddDer (D ∘ₗ E - E ∘ₗ D) where
  mul u v := by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, hD.mul, hE.mul, map_add, hE.parity]
    noncomm_ring
  parity u := by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, hD.parity, hE.parity, map_neg,
      map_sub]
    abel

/-- The anticommutator of two odd derivations is even. -/
theorem IsOddDer.anticommutator {D D' : Cochain →ₗ[ℂ] Cochain} (hD : IsOddDer D)
    (hD' : IsOddDer D') : IsEvenDer (D ∘ₗ D' + D' ∘ₗ D) where
  mul u v := by
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hD.mul, hD'.mul, map_add,
      hD.parity, hD'.parity, cochainParity_involutive, neg_mul]
    noncomm_ring
  parity u := by
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hD.parity, hD'.parity, map_neg,
      neg_neg, map_add]

/-- The commutator of two even derivations is even. -/
theorem IsEvenDer.commutator {E E' : Cochain →ₗ[ℂ] Cochain} (hE : IsEvenDer E)
    (hE' : IsEvenDer E') : IsEvenDer (E ∘ₗ E' - E' ∘ₗ E) where
  mul u v := by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, hE.mul, hE'.mul, map_add]
    noncomm_ring
  parity u := by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, hE.parity, hE'.parity, map_sub]

theorem IsOddDer.add {D D' : Cochain →ₗ[ℂ] Cochain} (hD : IsOddDer D) (hD' : IsOddDer D') :
    IsOddDer (D + D') where
  mul u v := by simp only [LinearMap.add_apply, hD.mul, hD'.mul]; noncomm_ring
  parity u := by simp only [LinearMap.add_apply, hD.parity, hD'.parity, map_add, neg_add]

theorem IsEvenDer.add {E E' : Cochain →ₗ[ℂ] Cochain} (hE : IsEvenDer E) (hE' : IsEvenDer E') :
    IsEvenDer (E + E') where
  mul u v := by simp only [LinearMap.add_apply, hE.mul, hE'.mul]; noncomm_ring
  parity u := by simp only [LinearMap.add_apply, hE.parity, hE'.parity, map_add]

theorem IsOddDer.smul {D : Cochain →ₗ[ℂ] Cochain} (hD : IsOddDer D) (r : ℂ) :
    IsOddDer (r • D) where
  mul u v := by
    simp only [LinearMap.smul_apply, hD.mul, smul_add, smul_mul_assoc, mul_smul_comm]
  parity u := by simp only [LinearMap.smul_apply, hD.parity, map_smul, smul_neg]

theorem IsEvenDer.smul {E : Cochain →ₗ[ℂ] Cochain} (hE : IsEvenDer E) (r : ℂ) :
    IsEvenDer (r • E) where
  mul u v := by
    simp only [LinearMap.smul_apply, hE.mul, smul_add, smul_mul_assoc, mul_smul_comm]
  parity u := by simp only [LinearMap.smul_apply, hE.parity, map_smul]

theorem isOddDer_q : IsOddDer q := ⟨q_mul, q_parity⟩

theorem isEvenDer_colorAction (a : Fin 3) : IsEvenDer (colorAction a) :=
  ⟨colorAction_mul a, colorAction_parity a⟩

end KhanSL2
