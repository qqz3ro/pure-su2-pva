module

public import KhanSL2.BGG.CurrentCoordinates
public import KhanSL2.Modules.CoefficientOperators
public import Mathlib.Algebra.Polynomial.Eval.SMul

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Ordinary evaluation of polynomial currents, including nonzero points.
This uses finite polynomial evaluation, not substitution into a completed or
restricted-dual cochain space. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald

/-- Polynomial-current evaluation as a linear map. -/
def currentEvaluationLinear (a : ℂ) : BGG.Current →ₗ[ℂ] BGG.G :=
  (TensorProduct.lid ℂ BGG.G).toLinearMap.comp ((Polynomial.leval a).rTensor BGG.G)

@[simp] theorem currentEvaluationLinear_tmul (a : ℂ) (f : Polynomial ℂ) (x : BGG.G) :
    currentEvaluationLinear a (f ⊗ₜ[ℂ] x) = f.eval a • x := by
  simp [currentEvaluationLinear]

/-- Evaluation at any complex point is a homomorphism of the actual Lie algebras. -/
def currentEvaluation (a : ℂ) : BGG.Current →ₗ⁅ℂ⁆ BGG.G where
  toLinearMap := currentEvaluationLinear a
  map_lie' := by
    intro u v
    change currentEvaluationLinear a ⁅u,v⁆ =
      ⁅currentEvaluationLinear a u,currentEvaluationLinear a v⁆
    induction u using TensorProduct.induction_on with
    | zero => simp [BGG.current_zero_lie, BGG.current_lie_zero]
    | add u w hu hw => simp only [LieRing.add_lie, map_add, hu, hw]
    | tmul f x =>
      induction v using TensorProduct.induction_on with
      | zero => simp [BGG.current_zero_lie, BGG.current_lie_zero]
      | add v w hv hw => simp only [LieRing.lie_add, map_add, hv, hw]
      | tmul g y =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul, currentEvaluationLinear_tmul,
          Polynomial.eval_mul, smul_lie, lie_smul, smul_smul]
        rw [mul_comm]

@[simp] theorem currentEvaluation_tmul (a : ℂ) (f : Polynomial ℂ) (x : BGG.G) :
    currentEvaluation a (f ⊗ₜ[ℂ] x) = f.eval a • x :=
  currentEvaluationLinear_tmul a f x

@[simp] theorem currentEvaluation_mode (a : ℂ) (n : ℕ) (x : BGG.G) :
    currentEvaluation a (BGG.mode n x) = a ^ n • x := by
  simp [BGG.mode_apply]

@[simp] theorem currentEvaluation_constant (a : ℂ) (x : BGG.G) :
    currentEvaluation a (BGG.constant x) = x := by
  simp [BGG.constant_apply]

theorem currentEvaluation_surjective (a : ℂ) : Function.Surjective (currentEvaluation a) :=
  fun x => ⟨BGG.constant x,currentEvaluation_constant a x⟩

/-- Raising a current mode becomes multiplication by the corresponding scalar power. -/
theorem currentEvaluation_coefficientShift (a : ℂ) (m : ℕ) (x : BGG.Current) :
    currentEvaluation a (Modules.coefficientShift m x) = a ^ m • currentEvaluation a x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul f y =>
    simp only [Modules.coefficientShift_tmul, currentEvaluation_tmul,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, smul_smul]

/-- Currents divisible by z-a vanish under evaluation. -/
@[simp] theorem currentEvaluation_vanishingFactor (a : ℂ) (f : Polynomial ℂ) (x : BGG.G) :
    currentEvaluation a (((Polynomial.X - Polynomial.C a) * f) ⊗ₜ[ℂ] x) = 0 := by
  simp

/-- A separate type for a finite-dimensional constant representation evaluated at a point. -/
def Evaluation (_a : ℂ) (V : Type*) : Type _ := V

instance (a : ℂ) (V : Type*) [AddCommGroup V] : AddCommGroup (Evaluation a V) :=
  inferInstanceAs (AddCommGroup V)
instance (a : ℂ) (V : Type*) [AddCommGroup V] [Module ℂ V] : Module ℂ (Evaluation a V) :=
  inferInstanceAs (Module ℂ V)

instance (a : ℂ) (V : Type*) [AddCommGroup V] [LieRingModule BGG.G V] :
    LieRingModule BGG.Current (Evaluation a V) :=
  LieRingModule.compLieHom V (currentEvaluation a)

instance (a : ℂ) (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule BGG.G V] [LieModule ℂ BGG.G V] :
    LieModule ℂ BGG.Current (Evaluation a V) :=
  LieModule.compLieHom V (currentEvaluation a)

/-- The underlying vector space of an evaluation module is unchanged. -/
def evaluationEquiv (a : ℂ) (V : Type*) [AddCommGroup V] [Module ℂ V] :
    Evaluation a V ≃ₗ[ℂ] V := LinearEquiv.refl ℂ V

instance (a : ℂ) (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    FiniteDimensional ℂ (Evaluation a V) := inferInstanceAs (FiniteDimensional ℂ V)

@[simp] theorem evaluation_lie (a : ℂ) (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule BGG.G V] [LieModule ℂ BGG.G V]
    (x : BGG.Current) (v : Evaluation a V) :
    evaluationEquiv a V ⁅x,v⁆ = ⁅currentEvaluation a x,evaluationEquiv a V v⁆ := rfl

@[simp] theorem evaluation_mode_lie (a : ℂ) (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule BGG.G V] [LieModule ℂ BGG.G V]
    (n : ℕ) (x : BGG.G) (v : Evaluation a V) :
    evaluationEquiv a V ⁅BGG.mode n x,v⁆ = a ^ n • ⁅x,evaluationEquiv a V v⁆ := by
  rw [evaluation_lie, currentEvaluation_mode, smul_lie]

/-- Evaluation modules are annihilated by the current ideal (z-a)g[z]. -/
theorem evaluation_vanishingFactor_lie (a : ℂ) (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule BGG.G V] [LieModule ℂ BGG.G V]
    (f : Polynomial ℂ) (x : BGG.G) (v : Evaluation a V) :
    ⁅((Polynomial.X - Polynomial.C a) * f) ⊗ₜ[ℂ] x,v⁆ = 0 := by
  apply (evaluationEquiv a V).injective
  rw [map_zero, evaluation_lie, currentEvaluation_vanishingFactor, zero_lie]

end KhanSL2.Macdonald
