module

public import KhanSL2.SymmetricFamily.RootBaseChange
public import KhanSL2.SymmetricFamily.Assignments
public import KhanSL2.PolynomialBGG.RootRingFree
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The exact root-assignment splitting with the requested factor degree.
Nontriviality of the base-changed root ring is proved using its nonzero free module. -/

noncomputable section
open Polynomial
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Factorization.WeightedRoots

variable (k : ℕ) (A : Type) [CommRing A] [Algebra (Depth.RB k) A]

/-- The labelled-root extension stays nonzero after every nonzero coefficient base change. -/
theorem rootBase_nontrivial [Nontrivial A] : Nontrivial (RootBase k A) := by
  let : Nontrivial (RootPolynomial k) :=
    inferInstanceAs (Nontrivial (MvPolynomial (Fin k) ℂ))
  change Nontrivial (A ⊗[Depth.RB k] RootPolynomial k)
  infer_instance

/-- A chart with a positive-degree monic factor already has a nonzero coefficient ring. -/
theorem chart_nontrivial {r s : ℕ} (c : Collision.ChartData k r s A) (hr : 0 < r) :
    Nontrivial A := by
  rcases subsingleton_or_nontrivial A with h | h
  · let := h
    have hf : c.f₁ = 0 := Subsingleton.elim _ _
    have he : r = 0 := by rw [← c.degree₁, hf, Polynomial.natDegree_zero]
    omega
  · exact h

/-- The actual mapped factor retains its specified degree over the labelled-root extension. -/
theorem baseRoot_first_degree [Nontrivial A] {r s : ℕ} (c : Collision.ChartData k r s A) :
    (c.f₁.map (algebraMap A (RootBase k A))).natDegree = r := by
  let := rootBase_nontrivial k A
  exact (c.monic₁.natDegree_map _).trans c.degree₁

/-- The precise decomposition indexed by r-element subsets of labelled slots. -/
def rootAssignmentSplitting [Nontrivial A] {r s : ℕ} (c : Collision.ChartData k r s A) :
    RootBase k A ≃ₐ[A] ∀ S : Assignment k r,
      FactorRing (c.f₁.map (algebraMap A (RootBase k A)))
        (c.f₂.map (algebraMap A (RootBase k A))) (baseRoot k A) (fun _ => 1) S.val := by
  let f₁ := c.f₁.map (algebraMap A (RootBase k A))
  let f₂ := c.f₂.map (algebraMap A (RootBase k A))
  change RootBase k A ≃ₐ[A] ∀ S : Assignment k r,
    FactorRing f₁ f₂ (baseRoot k A) (fun _ => 1) S.val
  have hd : f₁.natDegree = r := baseRoot_first_degree k A c
  rw [← hd]
  exact (baseRootSplitting k A c).trans
    (AlgEquiv.piCongrLeft A (fun S : Assignment k f₁.natDegree =>
      FactorRing f₁ f₂ (baseRoot k A) (fun _ => 1) S.val)
      (assignmentEquiv k f₁.natDegree))

end KhanSL2.SymmetricFamily
