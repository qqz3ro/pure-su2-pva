module

public import KhanSL2.Macdonald.WeightedFactorRootScalars
public import KhanSL2.Macdonald.RootWeightedBlockRestriction

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped TensorProduct
namespace KhanSL2.Macdonald
open Factorization.WeightedRootModel
open scoped WeightedFactorScalars

variable {q₁ q₂ r₁ r₂ : ℕ} {A : Type} [CommRing A]
variable [Algebra (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) A] [Algebra ℂ A]
variable [IsScalarTower ℂ (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) A]
variable (c : Collision.ChartData ((q₁+q₂)+2*(r₁+r₂)) (q₁+2*r₁) (q₂+2*r₂) A)

/-- Independently insert each original weighted alphabet into its prescribed factor root algebra. -/
def weightedFactorRootTensorUnit :
    LabelledWeightedRing q₁ r₁ ⊗[ℂ] LabelledWeightedRing q₂ r₂ →ₐ[ℂ] BlockRootTensor c :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft : FactorRoots q₁ r₁ c.f₁ →ₐ[A] BlockRootTensor c).restrictScalars ℂ).comp
      (weightedFactorRootUnit q₁ r₁ c.f₁))
    (((Algebra.TensorProduct.includeRight : FactorRoots q₂ r₂ c.f₂ →ₐ[A] BlockRootTensor c).restrictScalars ℂ).comp
      (weightedFactorRootUnit q₂ r₂ c.f₂)) (fun _ _ => Commute.all _ _)

omit [IsScalarTower ℂ (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) A] in
@[simp] theorem weightedFactorRootTensorUnit_tmul
    (p : LabelledWeightedRing q₁ r₁) (t : LabelledWeightedRing q₂ r₂) :
    weightedFactorRootTensorUnit c (p ⊗ₜ[ℂ] t) =
      weightedFactorRootUnit q₁ r₁ c.f₁ p ⊗ₜ[A] weightedFactorRootUnit q₂ r₂ c.f₂ t := by
  simp [weightedFactorRootTensorUnit]

/-- The literal quotient-root restriction after canonical insertion of the original weighted alphabet. -/
def weightedChartRootUnit :
    LabelledWeightedRing (q₁+q₂) (r₁+r₂) →ₐ[ℂ] BlockRootTensor c :=
  ((blockRestriction c).restrictScalars ℂ).comp ((weightedBaseRight (q₁+q₂) (r₁+r₂) A).restrictScalars ℂ)

@[simp] theorem weightedChartRootUnit_X_first (i : Fin q₁ ⊕ Fin r₁) :
    weightedChartRootUnit c (MvPolynomial.X (firstWeightedInclusion q₁ q₂ r₁ r₂ i)) =
      factorRoot q₁ r₁ c.f₁ i ⊗ₜ[A] 1 :=
  blockRestriction_firstRoot c i

@[simp] theorem weightedChartRootUnit_X_second (i : Fin q₂ ⊕ Fin r₂) :
    weightedChartRootUnit c (MvPolynomial.X (secondWeightedInclusion q₁ q₂ r₁ r₂ i)) =
      1 ⊗ₜ[A] factorRoot q₂ r₂ c.f₂ i :=
  blockRestriction_secondRoot c i

/-- The raw block restriction used in the homology formula is exactly the original chart quotient restriction. -/
theorem weightedRootPolynomialBlock_chart (p : LabelledWeightedRing (q₁+q₂) (r₁+r₂)) :
    weightedFactorRootTensorUnit c (weightedRootPolynomialBlock q₁ q₂ r₁ r₂ p) =
      weightedChartRootUnit c p := by
  have he : (weightedFactorRootTensorUnit c).comp (weightedRootPolynomialBlock q₁ q₂ r₁ r₂) =
      weightedChartRootUnit c := by
    have h₁ (i : Fin q₁ ⊕ Fin r₁) :
        ((weightedFactorRootTensorUnit c).comp (weightedRootPolynomialBlock q₁ q₂ r₁ r₂))
          (MvPolynomial.X (firstWeightedInclusion q₁ q₂ r₁ r₂ i)) =
        weightedChartRootUnit c (MvPolynomial.X (firstWeightedInclusion q₁ q₂ r₁ r₂ i)) := by
      simp only [AlgHom.comp_apply,weightedRootPolynomialBlock_X_first,
        weightedChartRootUnit_X_first]
      exact (weightedFactorRootTensorUnit_tmul c (show LabelledWeightedRing q₁ r₁ from MvPolynomial.X i) 1).trans
        (by rw [weightedFactorRootUnit_X,map_one])
    have h₂ (i : Fin q₂ ⊕ Fin r₂) :
        ((weightedFactorRootTensorUnit c).comp (weightedRootPolynomialBlock q₁ q₂ r₁ r₂))
          (MvPolynomial.X (secondWeightedInclusion q₁ q₂ r₁ r₂ i)) =
        weightedChartRootUnit c (MvPolynomial.X (secondWeightedInclusion q₁ q₂ r₁ r₂ i)) := by
      simp only [AlgHom.comp_apply,weightedRootPolynomialBlock_X_second,
        weightedChartRootUnit_X_second]
      exact (weightedFactorRootTensorUnit_tmul c 1 (show LabelledWeightedRing q₂ r₂ from MvPolynomial.X i)).trans
        (by rw [weightedFactorRootUnit_X,map_one])
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | inl i => exact Fin.addCases (fun j => h₁ (.inl j)) (fun j => h₂ (.inl j)) i
    | inr i => exact Fin.addCases (fun j => h₁ (.inr j)) (fun j => h₂ (.inr j)) i
  exact AlgHom.congr_fun he p

end KhanSL2.Macdonald
