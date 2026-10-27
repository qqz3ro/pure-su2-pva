module

public import KhanSL2.Macdonald.SymmetricCoefficients
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.RingTheory.Derivation.Lie

@[expose] public section

/-! The adjoint current action on the actual symmetric algebra. Every linear
endomorphism of the current space extends to a polynomial derivation, and this
extension respects commutators. No current action is installed on cochain `Poly`. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.Macdonald

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Extend a current-space endomorphism by the Leibniz rule. -/
def symmetricDerivation (D : Module.End ℂ BGG.Current) : Derivation ℂ Poly Poly :=
  MvPolynomial.mkDerivation ℂ (fun m => currentVariable (D (symmetricCurrentBasis m)))

@[simp] theorem symmetricDerivation_X (D : Module.End ℂ BGG.Current) (m : Mode) :
    symmetricDerivation D (MvPolynomial.X m) =
      currentVariable (D (symmetricCurrentBasis m)) :=
  MvPolynomial.mkDerivation_X _ _ _

/-- Extension acts as the given endomorphism on the whole current vector space. -/
theorem symmetricDerivation_currentVariable (D : Module.End ℂ BGG.Current)
    (x : BGG.Current) :
    symmetricDerivation D (currentVariable x) = currentVariable (D x) := by
  have h : (symmetricDerivation D).toLinearMap.comp currentVariable =
      currentVariable.comp D := by
    apply symmetricCurrentBasis.ext
    intro m
    change symmetricDerivation D (currentVariable (symmetricCurrentBasis m)) =
      currentVariable (D (symmetricCurrentBasis m))
    rw [currentVariable_basis, symmetricDerivation_X]
  exact LinearMap.congr_fun h x

/-- Linear extension to the symmetric algebra is a Lie-algebra homomorphism. -/
def extendCurrentEnd : Module.End ℂ BGG.Current →ₗ⁅ℂ⁆ Derivation ℂ Poly Poly where
  toFun := symmetricDerivation
  map_add' D E := by
    apply MvPolynomial.derivation_ext
    intro m
    simp
  map_smul' c D := by
    apply MvPolynomial.derivation_ext
    intro m
    simp
  map_lie' {D E} := by
    apply MvPolynomial.derivation_ext
    intro m
    simp only [symmetricDerivation_X, Derivation.commutator_apply,
      symmetricDerivation_currentVariable]
    change currentVariable (D (E (symmetricCurrentBasis m)) -
      E (D (symmetricCurrentBasis m))) = _
    exact map_sub currentVariable _ _

/-- The actual adjoint current action on symmetric coefficients. -/
def currentAction : BGG.Current →ₗ⁅ℂ⁆ Derivation ℂ Poly Poly :=
  extendCurrentEnd.comp (LieAlgebra.ad ℂ BGG.Current)

@[simp] theorem currentAction_currentVariable (x y : BGG.Current) :
    currentAction x (currentVariable y) = currentVariable ⁅x,y⁆ :=
  symmetricDerivation_currentVariable (LieAlgebra.ad ℂ BGG.Current x) y

/-- The explicit raising formula in epsilon-normalized color coordinates. -/
theorem currentAction_mode_X (j n : ℕ) (a b : Fin 3) :
    currentAction (BGG.mode j (MatrixSL2.color a)) (MvPolynomial.X (⟨n,b⟩ : Mode)) =
      ∑ c : Fin 3, epsilon a b c • MvPolynomial.X (⟨j+n,c⟩ : Mode) := by
  rw [← currentVariable_mode n b, currentAction_currentVariable, BGG.mode_lie,
    MatrixSL2.color_bracket, map_sum, map_sum]
  simp only [map_smul, currentVariable_mode]

/-- The Lie representation identity on every symmetric polynomial. -/
theorem currentAction_bracket (x y : BGG.Current) (p : Poly) :
    currentAction ⁅x,y⁆ p =
      currentAction x (currentAction y p) - currentAction y (currentAction x p) :=
  congrArg (fun D : Derivation ℂ Poly Poly => D p) (currentAction.map_lie x y)

/-- The current acts by actual polynomial derivations. -/
theorem currentAction_mul (x : BGG.Current) (p q : Poly) :
    currentAction x (p*q) = currentAction x p * q + p * currentAction x q := by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

end KhanSL2.Macdonald
