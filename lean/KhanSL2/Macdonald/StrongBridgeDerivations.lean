module

public import KhanSL2.Macdonald.StrongBridgeExterior
public import KhanSL2.Macdonald.CurrentAdjoint

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Transport of actual polynomial vector fields to the imported algebra model. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.Macdonald

/-- Extend an even polynomial vector field trivially on exterior coefficients. -/
def tensorPolynomialDerivation (D : Derivation ℂ Poly Poly) : Module.End ℂ W :=
  TensorProduct.map D.toLinearMap LinearMap.id

@[simp] theorem tensorPolynomialDerivation_tmul (D : Derivation ℂ Poly Poly)
    (p : Poly) (ω : Exterior) :
    tensorPolynomialDerivation D (p ⊗ₜ[ℂ] ω) = D p ⊗ₜ[ℂ] ω := rfl

theorem tensorPolynomialDerivation_mul (D : Derivation ℂ Poly Poly) (u v : W) :
    tensorPolynomialDerivation D (u*v) =
      tensorPolynomialDerivation D u * v + u * tensorPolynomialDerivation D v := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul p ω =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul q η =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, tensorPolynomialDerivation_tmul,
        Derivation.leibniz, smul_eq_mul, TensorProduct.add_tmul]
      rw [mul_comm q (D p)]
      abel
    | add v w hv hw => simp only [mul_add, map_add, hv, hw, add_mul]; abel
  | add u w hu hw => simp only [add_mul, map_add, hu, hw, mul_add]; abel

/-- The same vector field in exterior-valued polynomial coordinates. -/
def strongPolynomialDerivation (D : Derivation ℂ Poly Poly) :
    Module.End ℂ StrongMacdonald.W :=
  strongModel.symm.toLinearMap.comp ((tensorPolynomialDerivation D).comp strongModel.toLinearMap)

@[simp] theorem strongModel_polynomialDerivation (D : Derivation ℂ Poly Poly)
    (u : StrongMacdonald.W) :
    strongModel (strongPolynomialDerivation D u) = tensorPolynomialDerivation D (strongModel u) := by
  simp [strongPolynomialDerivation]

theorem strongPolynomialDerivation_isDer (D : Derivation ℂ Poly Poly) :
    StrongMacdonald.IsDer 0 (strongPolynomialDerivation D) := by
  intro u v
  apply strongModel.injective
  simpa only [strongModel_polynomialDerivation, strongModel_mul, map_add,
    Function.iterate_zero, id_eq] using
    tensorPolynomialDerivation_mul D (strongModel u) (strongModel v)

/-- The imported lowering action is exactly the polynomial coadjoint action. -/
theorem strongRlow_eq (a : Fin 3) (m : ℕ) :
    StrongMacdonald.Rlow a m = strongPolynomialDerivation (currentLower m a) := by
  apply (StrongMacdonald.homDer_Rlow a m).isDer.ext (strongPolynomialDerivation_isDer _)
  intro g
  apply strongModel.injective
  cases g with
  | s g =>
    obtain ⟨n,b⟩ := g
    change strongModel (StrongMacdonald.Rlow a m (StrongMacdonald.sigOf n b)) =
      strongModel (strongPolynomialDerivation (currentLower m a) (StrongMacdonald.sigOf n b))
    rw [StrongMacdonald.Rlow_sigOf, strongModel_polynomialDerivation]
    simp only [strongModel_sigOf, sigma, tensorPolynomialDerivation_tmul, currentLower_X]
    split <;> simp [sigma, TensorProduct.sum_tmul, TensorProduct.smul_tmul']
  | p g =>
    change strongModel (StrongMacdonald.Rlow a m (StrongMacdonald.psiOf g.index g.color)) =
      strongModel (strongPolynomialDerivation (currentLower m a) (StrongMacdonald.psiOf g.index g.color))
    rw [StrongMacdonald.Rlow_psiOf, map_zero, strongModel_polynomialDerivation]
    simp [psi]

/-- Pointwise operator compatibility for later finite sums. -/
theorem strongModel_Rlow (a : Fin 3) (m : ℕ) (u : StrongMacdonald.W) :
    strongModel (StrongMacdonald.Rlow a m u) =
      tensorPolynomialDerivation (currentLower m a) (strongModel u) := by
  rw [strongRlow_eq, strongModel_polynomialDerivation]

end KhanSL2.Macdonald
