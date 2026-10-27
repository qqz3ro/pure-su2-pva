module

public import KhanSL2.Factorization.WeightedRootsSplitting
public import Mathlib.Algebra.Algebra.Pi

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
namespace KhanSL2.Factorization.WeightedRoots

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coefficient-ideal splitting respects every given coefficient algebra.
Its components are the original quotient maps, so scalar compatibility is explicit. -/
def weightedSplittingAlgEquivOfCoprime {f₁ f₂ : A[X]}
    (hf₁ : f₁.Monic) (hf₂ : f₂.Monic) (hcop : IsCoprime f₁ f₂)
    (x : ι → A) (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hprod : rootProduct x m Finset.univ = f₁*f₂) :
    A ≃ₐ[R] ∀ σ : Admissible m f₁.natDegree,
      FactorRing f₁ f₂ x m (selected σ.val) where
  __ := weightedSplittingEquivOfCoprime hf₁ hf₂ hcop x m hm hprod
  commutes' r := by
    funext σ
    exact weightedSplittingEquivOfCoprime_apply hf₁ hf₂ hcop x m hm hprod (algebraMap R A r) σ

@[simp] theorem weightedSplittingAlgEquivOfCoprime_apply {f₁ f₂ : A[X]}
    (hf₁ : f₁.Monic) (hf₂ : f₂.Monic) (hcop : IsCoprime f₁ f₂)
    (x : ι → A) (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hprod : rootProduct x m Finset.univ = f₁*f₂) (a : A)
    (σ : Admissible m f₁.natDegree) :
    weightedSplittingAlgEquivOfCoprime (R := R) hf₁ hf₂ hcop x m hm hprod a σ =
      Ideal.Quotient.mk _ a :=
  weightedSplittingEquivOfCoprime_apply hf₁ hf₂ hcop x m hm hprod a σ

end KhanSL2.Factorization.WeightedRoots
