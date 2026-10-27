module

public import KhanSL2.Factorization.ShuffleComplex
public import KhanSL2.Factorization.CoefficientMaps
public import KhanSL2.Macdonald.SymmetricCoefficientsComponents

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The actual symmetric-coefficient coproduct followed by the canonical relative
CE shuffle. Both constituent maps have already been specified on generators. -/

noncomputable section
open scoped TensorProduct
open CategoryTheory
namespace KhanSL2.Factorization
open KhanSL2.Macdonald

/-- The canonical coproduct on actual relative CE chains with symmetric coefficients. -/
def symmetricChainCoproduct :
    RelativeChains SymmetricCoefficients →ₗ[ℂ]
      RelativeChains SymmetricCoefficients ⊗[ℂ] RelativeChains SymmetricCoefficients :=
  (relativeShuffle SymmetricCoefficients SymmetricCoefficients).comp
    (coefficientMap symmetricCoproduct.toLinearMap
      (constantEquivariant_of_lieHom symmetricCoproduct))

/-- The actual symmetric CE coproduct commutes with its specified signed boundary. -/
theorem symmetricChainCoproduct_differential (z : RelativeChains SymmetricCoefficients) :
    symmetricChainCoproduct (differential SymmetricCoefficients z) =
      relativeTensorDifferential SymmetricCoefficients SymmetricCoefficients
        (symmetricChainCoproduct z) := by
  simp only [symmetricChainCoproduct, LinearMap.comp_apply,
    coefficientMap_differential, relativeShuffle_differential]

/-- The same canonical symmetric-chain coproduct packaged as a genuine tensor-complex map. -/
def symmetricCoproductComplex : complex SymmetricCoefficients ⟶
    tensorComplex SymmetricCoefficients SymmetricCoefficients :=
  complexMap symmetricCoproduct ≫ shuffleComplex SymmetricCoefficients SymmetricCoefficients

/-- Its categorical component is exactly the previously specified chain coproduct. -/
theorem symmetricCoproductComplex_component (j : ℕ)
    (z : degree SymmetricCoefficients j) :
    tensorDegreeForget SymmetricCoefficients SymmetricCoefficients j
      ((symmetricCoproductComplex.f j) z) = symmetricChainCoproduct z.val := by
  change tensorDegreeForget SymmetricCoefficients SymmetricCoefficients j
    (degreeShuffle SymmetricCoefficients SymmetricCoefficients j
      (coefficientDegreeMap symmetricCoproduct.toLinearMap
        (constantEquivariant_of_lieHom symmetricCoproduct) j z)) = _
  rw [tensorDegreeForget_degreeShuffle]
  rfl

/-- The fixed coefficient-bidegree component, with the actual primitive coproduct
and actual canonical CE shuffle. -/
def symmetricPowerCoproductComplex (k₁ k₂ : ℕ) :
    complex (symmetricPower (k₁+k₂)) ⟶
      tensorComplex (symmetricPower k₁) (symmetricPower k₂) :=
  complexMap (symmetricCoproductComponent k₁ k₂) ≫
    shuffleComplex (symmetricPower k₁) (symmetricPower k₂)

end KhanSL2.Factorization
