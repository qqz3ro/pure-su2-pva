module

public import KhanSL2.Macdonald.StrongBridgeFreeRaisingExterior
public import KhanSL2.Macdonald.StrongBridgeFreeAction

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Explicit raising on the free Macdonald coordinates.  Its even generator
weight is two and odd generator weight is one.  The actual factorial/exterior
pairing identifies it with the already specified lowering operator. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald

/-- Sum of derivations on the two tensor factors, with specified even weight. -/
def freeMixedShift (A : Derivation ℂ Poly Poly) (B : Module.End ℂ Exterior) :
    Module.End ℂ W :=
  (2 : ℂ) • TensorProduct.map A.toLinearMap LinearMap.id +
    TensorProduct.map LinearMap.id B

@[simp] theorem freeMixedShift_tmul (A : Derivation ℂ Poly Poly)
    (B : Module.End ℂ Exterior) (p : Poly) (ω : Exterior) :
    freeMixedShift A B (p ⊗ₜ[ℂ] ω) =
      (2 : ℂ) • (A p ⊗ₜ[ℂ] ω) + p ⊗ₜ[ℂ] B ω := rfl

theorem freeMixedShift_one (A : Derivation ℂ Poly Poly) (B : Module.End ℂ Exterior)
    (hB : B 1 = 0) : freeMixedShift A B 1 = 0 := by
  simp [Algebra.TensorProduct.one_def, hB]

theorem freeMixedShift_mul (A : Derivation ℂ Poly Poly) (B : Module.End ℂ Exterior)
    (hB : ∀ u v, B (u*v) = B u*v + u*B v) (u v : W) :
    freeMixedShift A B (u*v) = freeMixedShift A B u*v + u*freeMixedShift A B v := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul p ω =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul q η =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, freeMixedShift_tmul,
        Derivation.leibniz, smul_eq_mul, hB, TensorProduct.add_tmul,
        TensorProduct.tmul_add, smul_add, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
      rw [mul_comm q (A p)]
      module
    | add v w hv hw => simp only [mul_add, map_add, hv, hw, add_mul]; module
  | add u w hu hw => simp only [add_mul, map_add, hu, hw, mul_add]; module

/-- The concrete raising operator on finite polynomial/exterior coordinates. -/
def freeMixedRaise (m : ℕ) : Module.End ℂ W :=
  freeMixedShift (symmetricCoefficientShift m) (freeOddRaise m)

/-- The corresponding concrete lowering operator, with both boundary rules. -/
def freeMixedLower (m : ℕ) : Module.End ℂ W :=
  freeMixedShift (polynomialShift m) (freeOddLower m)

@[simp] theorem freeMixedRaise_sigma (m : ℕ) (a : Fin 3) (n : ℕ) :
    freeMixedRaise m (sigma a n) = (2 : ℂ) • sigma a (n+m) := by
  simp [freeMixedRaise, sigma, Nat.add_comm]

@[simp] theorem freeMixedRaise_psi (m : ℕ) (a : Fin 3) (i : ℕ) :
    freeMixedRaise m (psi a i) = psi a (i+m) := by
  simp [freeMixedRaise, psi, freeOddRaiseGenerator]

@[simp] theorem freeMixedLower_sigma (m : ℕ) (a : Fin 3) (n : ℕ) :
    freeMixedLower m (sigma a n) = if m ≤ n then (2 : ℂ) • sigma a (n-m) else 0 := by
  simp only [freeMixedLower, sigma, freeMixedShift_tmul, polynomialShift_X,
    LinearMap.id_apply, freeOddLower_one, TensorProduct.tmul_zero, add_zero]
  split <;> simp

@[simp] theorem freeMixedLower_psi (m : ℕ) (a : Fin 3) (i : ℕ) :
    freeMixedLower m (psi a i) = if m ≤ i then psi a (i-m) else 0 := by
  simp only [freeMixedLower, psi, freeMixedShift_tmul, Derivation.map_one_eq_zero,
    TensorProduct.zero_tmul, smul_zero, zero_add, freeOddLower_generator, freeOddLowerGenerator]
  split <;> simp

theorem freeMixedRaise_adjoint (m : ℕ) (u v : W) :
    pairing (freeMixedRaise m u) v = pairing u (freeMixedLower m v) := by
  have hp := coefficientShift_pairing m u v
  have he := pairing_tensor_map LinearMap.id LinearMap.id
    (freeOddRaise m) (freeOddLower m) (fun _ _ => rfl) (freeOddRaise_adjoint m) u v
  simp only [freeMixedRaise, freeMixedLower, freeMixedShift, LinearMap.add_apply,
    LinearMap.smul_apply, map_add, map_smul]
  change (2 : ℂ) • pairing (chainCoefficientShift m u) v +
      pairing (TensorProduct.map LinearMap.id (freeOddRaise m) u) v =
    (2 : ℂ) • pairing u (coefficientShift m v) +
      pairing u (TensorProduct.map LinearMap.id (freeOddLower m) v)
  rw [hp, he]

/-- The source action is specified on generators before invoking any pairing. -/
def strongFreeRaise (m : ℕ) : Module.End ℂ StrongMacdonald.W :=
  StrongMacdonald.mkDer
    (fun g => (2 : ℂ) • StrongMacdonald.sigOf (g.index+m) g.color)
    (fun g => StrongMacdonald.psiOf (g.index+m) g.color)

theorem strongFreeRaise_homDer (m : ℕ) : StrongMacdonald.HomDer 0 (strongFreeRaise m) :=
  StrongMacdonald.mkDer_homDer _ _
    (fun _g => (StrongMacdonald.isPar_sigOf _ _).smul _)
    (fun _g => StrongMacdonald.isPar_psiOf _ _)

@[simp] theorem strongFreeRaise_sig (m : ℕ) (g : StrongMacdonald.SMode) :
    strongFreeRaise m (StrongMacdonald.sig g) =
      (2 : ℂ) • StrongMacdonald.sigOf (g.index+m) g.color :=
  StrongMacdonald.mkDer_sig _ _ _

@[simp] theorem strongFreeRaise_psi (m : ℕ) (g : Mode) :
    strongFreeRaise m (StrongMacdonald.psi g) =
      StrongMacdonald.psiOf (g.index+m) g.color :=
  StrongMacdonald.mkDer_psi _ _ _

/-- Concrete mixed derivation intertwining follows from its generator values. -/
theorem strongModel_evenDerivation (D : Module.End ℂ StrongMacdonald.W)
    (T : Module.End ℂ W) (hD : StrongMacdonald.HomDer 0 D) (hT1 : T 1 = 0)
    (hTm : ∀ u v, T (u*v) = T u*v + u*T v)
    (hs : ∀ g, T (strongModel (StrongMacdonald.sig g)) = strongModel (D (StrongMacdonald.sig g)))
    (hp : ∀ g, T (strongModel (StrongMacdonald.psi g)) = strongModel (D (StrongMacdonald.psi g)))
    (u : StrongMacdonald.W) : T (strongModel u) = strongModel (D u) := by
  refine StrongMacdonald.induction_gen (P := fun u => T (strongModel u) = strongModel (D u))
    ?_ ?_ ?_ ?_ ?_ ?_ u
  · simp
  · rw [strongModel_one, hT1, hD.map_one, map_zero]
  · intro u v hu hv
    simp only [map_add, hu, hv]
  · intro c u hu
    simp only [map_smul, hu]
  · intro g u hu
    rw [strongModel_mul, hTm, hs, hu, hD.zero_mul_apply, map_add,
      strongModel_mul, strongModel_mul]
  · intro g u hu
    rw [strongModel_mul, hTm, hp, hu, hD.zero_mul_apply, map_add,
      strongModel_mul, strongModel_mul]

/-- The specified raising is precisely the concrete raising on every coordinate. -/
theorem strongModel_freeRaise (m : ℕ) (u : StrongMacdonald.W) :
    freeMixedRaise m (strongModel u) = strongModel (strongFreeRaise m u) := by
  apply strongModel_evenDerivation (strongFreeRaise m) (freeMixedRaise m)
    (strongFreeRaise_homDer m)
    (freeMixedShift_one _ _ (freeOddRaise_one m))
    (freeMixedShift_mul _ _ (freeOddRaise_mul m))
  · intro g
    simp [StrongMacdonald.sigOf]
  · intro g
    simp [StrongMacdonald.psiOf]

/-- Both lowering boundary rules agree exactly under the coordinate map. -/
theorem strongModel_freeLower (m : ℕ) (u : StrongMacdonald.W) :
    freeMixedLower m (strongModel u) = strongModel (strongFreeLower m u) := by
  apply strongModel_evenDerivation (strongFreeLower m) (freeMixedLower m)
    (strongFreeLower_homDer m)
    (freeMixedShift_one _ _ (freeOddLower_one m))
    (freeMixedShift_mul _ _ (freeOddLower_mul m))
  · intro g
    simp only [strongModel_sig, freeMixedLower_sigma, strongFreeLower_sig]
    split <;> simp [StrongMacdonald.sigOf]
  · intro g
    simp only [strongModel_psi, freeMixedLower_psi, strongFreeLower_psi]
    split <;> simp [StrongMacdonald.psiOf]

/-- The source adjunction is an identity for the original finite coordinate pairing. -/
theorem strongFreeRaise_adjoint (m : ℕ) (u v : StrongMacdonald.W) :
    pairing (strongModel (strongFreeRaise m u)) (strongModel v) =
      pairing (strongModel u) (strongModel (strongFreeLower m v)) := by
  rw [← strongModel_freeRaise, ← strongModel_freeLower]
  exact freeMixedRaise_adjoint m _ _

/-- Raising preserves the actual colour-zero free subspace. -/
theorem strongFreeRaise_projFull (m : ℕ) (u : StrongMacdonald.W) :
    strongFreeRaise m (StrongMacdonald.projFull u) =
      StrongMacdonald.projFull (strongFreeRaise m u) := by
  apply strong_algHom_derivation_intertwining StrongMacdonald.projFull
    (strongFreeRaise m) (strongFreeRaise m)
    (strongFreeRaise_homDer m) (strongFreeRaise_homDer m)
  · intro g
    by_cases hc : g.color = 0 <;>
      simp [StrongMacdonald.projFull_sig, strongFreeRaise_sig, StrongMacdonald.sigOf, hc]
  · intro g
    by_cases hc : g.color = 0 <;>
      simp [StrongMacdonald.projFull_psi, strongFreeRaise_psi, StrongMacdonald.psiOf, hc]

/-- Restriction of the explicit derivation, not transport through a homology equivalence. -/
def strongFreeRaiseEnd (m : ℕ) : Module.End ℂ strongFree :=
  (strongFreeRaise m).restrict (by
    intro u hu
    change StrongMacdonald.projFull u = u at hu
    change StrongMacdonald.projFull (strongFreeRaise m u) = strongFreeRaise m u
    rw [← strongFreeRaise_projFull, hu])

@[simp] theorem strongFreeRaiseEnd_val (m : ℕ) (u : strongFree) :
    (strongFreeRaiseEnd m u).val = strongFreeRaise m u.val := rfl

theorem strongFreeRaiseEnd_adjoint (m : ℕ) (u v : strongFree) :
    pairing (strongModel (strongFreeRaiseEnd m u).val) (strongModel v.val) =
      pairing (strongModel u.val) (strongModel (strongFreeLowerEnd m v).val) :=
  strongFreeRaise_adjoint m u.val v.val

end KhanSL2.Macdonald
