module

public import KhanSL2.Macdonald.WeightedRootBlockEvaluation
public import KhanSL2.Macdonald.RootFreeWeightedCoproduct
public import KhanSL2.SymmetricFamily.FactorInsertion

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped TensorProduct
namespace KhanSL2.Macdonald
open Factorization WeightedRootModel
open scoped WeightedFactorScalars

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- Original root homology classes inserted into the specified factor coefficient specialization. -/
def weightedRootHomologyFactorUnit (q r : ℕ) (f : Polynomial A) :
    RootHomologyModel q r →ₗ[ℂ] FactorSignedModule q r f :=
  (weightedFactorSignedUnit q r f).comp (rootHomologyModelEquiv q r).toLinearMap

@[simp] theorem weightedRootHomologyFactorUnit_inclusion (q r : ℕ) (f : Polynomial A)
    (x : RootHomologyModel q r) :
    factorSignedInclusion q r f (weightedRootHomologyFactorUnit q r f x) =
      weightedFactorRootUnit q r f (rootHomologyWeightedMap q r x) := rfl

/-- The product of the two genuine signed invariant inclusions is faithful over arbitrary base rings. -/
theorem weightedFactorSignedTensorInclusion_injective (q₁ q₂ r₁ r₂ : ℕ) (f₁ f₂ : Polynomial A) :
    Function.Injective (TensorProduct.map (factorSignedInclusion q₁ r₁ f₁) (factorSignedInclusion q₂ r₂ f₂)) := by
  let E := (TensorProduct.congr (factorSignedEquiv q₁ r₁ f₁) (factorSignedEquiv q₂ r₂ f₂)).trans
    (FiberTransport.tensorFixedEquiv (factorSignedAction q₁ r₁ f₁) (factorSignedAction q₂ r₂ f₂)
      (factorNormalization q₁ r₁) (factorNormalization q₂ r₂)
      (factorNormalization_mul_card q₁ r₁) (factorNormalization_mul_card q₂ r₂))
  have he (z : FactorSignedModule q₁ r₁ f₁ ⊗[A] FactorSignedModule q₂ r₂ f₂) :
      (E z).val = TensorProduct.map (factorSignedInclusion q₁ r₁ f₁) (factorSignedInclusion q₂ r₂ f₂) z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add,Submodule.coe_add,hx,hy]
    | tmul x y => rfl
  intro x y h
  apply E.injective
  apply Subtype.ext
  rw [he,he]
  exact h

/-- Canonical factor specialization of the tensor of original root homology components. -/
def weightedRootHomologyTensorUnit (q₁ q₂ r₁ r₂ : ℕ) (f₁ f₂ : Polynomial A) :
    RootHomologyModel q₁ r₁ ⊗[ℂ] RootHomologyModel q₂ r₂ →ₗ[ℂ]
      FactorSignedModule q₁ r₁ f₁ ⊗[A] FactorSignedModule q₂ r₂ f₂ :=
  SymmetricFamily.tensorOverMap (weightedRootHomologyFactorUnit q₁ r₁ f₁)
    (weightedRootHomologyFactorUnit q₂ r₂ f₂)

variable {q₁ q₂ r₁ r₂ : ℕ}
variable [Algebra (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) A]
variable [IsScalarTower ℂ (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) A]
variable (c : Collision.ChartData ((q₁+q₂)+2*(r₁+r₂)) (q₁+2*r₁) (q₂+2*r₂) A)

omit [IsScalarTower ℂ (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) A] in
/-- Faithful signed factor coordinates commute with the canonical factor insertions. -/
theorem weightedRootHomologyTensorUnit_inclusion
    (z : RootHomologyModel q₁ r₁ ⊗[ℂ] RootHomologyModel q₂ r₂) :
    TensorProduct.map (factorSignedInclusion q₁ r₁ c.f₁) (factorSignedInclusion q₂ r₂ c.f₂)
      (weightedRootHomologyTensorUnit q₁ q₂ r₁ r₂ c.f₁ c.f₂ z) =
      weightedFactorRootTensorUnit c
        (TensorProduct.map (rootHomologyWeightedMap q₁ r₁) (rootHomologyWeightedMap q₂ r₂) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y =>
    simp only [weightedRootHomologyTensorUnit,SymmetricFamily.tensorOverMap_tmul,TensorProduct.map_tmul,
      weightedRootHomologyFactorUnit_inclusion,weightedFactorRootTensorUnit_tmul]

/-- The normalized root homology block specializes to the actual chart quotient restriction. -/
theorem rootHomologyNormalizedBlock_chart
    (x : RootHomologyModel (q₁+q₂) (r₁+r₂)) :
    TensorProduct.map (factorSignedInclusion q₁ r₁ c.f₁) (factorSignedInclusion q₂ r₂ c.f₂)
      (weightedRootHomologyTensorUnit q₁ q₂ r₁ r₂ c.f₁ c.f₂
        (rootHomologyNormalizedBlock q₁ q₂ r₁ r₂ x)) =
      weightedChartRootUnit c (rootHomologyWeightedMap (q₁+q₂) (r₁+r₂) x) := by
  rw [weightedRootHomologyTensorUnit_inclusion,rootHomologyNormalizedBlock_weighted,
    weightedRootPolynomialBlock_chart]

end KhanSL2.Macdonald
