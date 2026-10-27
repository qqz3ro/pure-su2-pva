module

public import KhanSL2.Macdonald.CurrentAction
public import KhanSL2.Modules.CoefficientOperators

@[expose] public section

/-! Raising coefficient operators on symmetric current coefficients.
These are distinct from the lowering operators on restricted cochain coordinates.
Both are explicit derivations; their transpose relation is a separate pairing theorem. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Derivation extension preserves commuting current-space endomorphisms. -/
theorem symmetricDerivation_commute {D E : Module.End ℂ BGG.Current}
    (h : Commute D E) :
    Commute (symmetricDerivation D).toLinearMap (symmetricDerivation E).toLinearMap := by
  have hDE : ⁅D,E⁆ = 0 := sub_eq_zero.mpr h.eq
  have h' : ⁅symmetricDerivation D,symmetricDerivation E⁆ = 0 := by
    rw [← show extendCurrentEnd D = symmetricDerivation D from rfl,
      ← show extendCurrentEnd E = symmetricDerivation E from rfl,
      ← LieHom.map_lie, hDE, map_zero]
  apply LinearMap.ext
  intro p
  have hp := congrArg (fun T : Derivation ℂ Poly Poly => T p) h'
  exact sub_eq_zero.mp hp

/-- Multiplication by z^m, extended by Leibniz to the actual symmetric algebra. -/
def symmetricCoefficientShift (m : ℕ) : Derivation ℂ Poly Poly :=
  symmetricDerivation (Modules.coefficientShift m)

@[simp] theorem symmetricCoefficientShift_currentVariable (m : ℕ) (x : BGG.Current) :
    symmetricCoefficientShift m (currentVariable x) =
      currentVariable (Modules.coefficientShift m x) :=
  symmetricDerivation_currentVariable _ _

@[simp] theorem symmetricCoefficientShift_X (m n : ℕ) (a : Fin 3) :
    symmetricCoefficientShift m (MvPolynomial.X (⟨n,a⟩ : Mode)) =
      MvPolynomial.X (⟨m+n,a⟩ : Mode) := by
  rw [← currentVariable_mode n a, symmetricCoefficientShift_currentVariable]
  have h : Modules.coefficientShift m (BGG.mode n (MatrixSL2.color a)) =
      BGG.mode (m+n) (MatrixSL2.color a) := Modules.coefficientShift_cur m n a
  rw [h, currentVariable_mode]

/-- The coefficient power sums commute with each other. -/
theorem symmetricCoefficientShift_commute (m n : ℕ) :
    Commute (symmetricCoefficientShift m).toLinearMap
      (symmetricCoefficientShift n).toLinearMap :=
  symmetricDerivation_commute (Modules.coefficientShift_commute m n)

/-- The coefficient power sums are endomorphisms for the full current action. -/
theorem symmetricCoefficientShift_currentAction (m : ℕ) (x : BGG.Current) (p : Poly) :
    symmetricCoefficientShift m (currentAction x p) =
      currentAction x (symmetricCoefficientShift m p) := by
  have h : Commute (Modules.coefficientShift m) (LieAlgebra.ad ℂ BGG.Current x) := by
    apply LinearMap.ext
    intro y
    exact Modules.coefficientShift_lie m x y
  exact LinearMap.congr_fun (symmetricDerivation_commute h).eq p

end KhanSL2.Macdonald
