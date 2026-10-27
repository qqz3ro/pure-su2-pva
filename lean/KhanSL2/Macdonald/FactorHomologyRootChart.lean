module

public import KhanSL2.Macdonald.FixedRootHomologyBaseChange
public import KhanSL2.Macdonald.RootDegreeAllocations

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped TensorProduct DirectSum
namespace KhanSL2.Macdonald
open Factorization WeightedRootModel Conditional

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- Scalar extension of original symmetric homology through the factor polynomial's original coefficient map. -/
def FactorSymmetricHomology (s : ℕ) (f : Polynomial A) : Type :=
  letI : Algebra (Depth.RB s) A := (Collision.coeffHom s f).toRingHom.toAlgebra
  A ⊗[Depth.RB s] TotalHomology (symmetricPower s)

instance (s : ℕ) (f : Polynomial A) : AddCommGroup (FactorSymmetricHomology s f) := by
  unfold FactorSymmetricHomology
  infer_instance
instance (s : ℕ) (f : Polynomial A) : Module A (FactorSymmetricHomology s f) := by
  unfold FactorSymmetricHomology
  infer_instance

/-- Scalar extension of one retained root block through the same factor coefficient map. -/
def FactorFixedRootBlock (s : ℕ) (f : Polynomial A) (d : RootHomologyDegrees s) : Type :=
  letI : Algebra (Depth.RB s) A := (Collision.coeffHom s f).toRingHom.toAlgebra
  A ⊗[Depth.RB s] FixedSignedRootModel s d

instance (s : ℕ) (f : Polynomial A) (d : RootHomologyDegrees s) : AddCommGroup (FactorFixedRootBlock s f d) := by
  unfold FactorFixedRootBlock
  infer_instance
instance (s : ℕ) (f : Polynomial A) (d : RootHomologyDegrees s) : Module A (FactorFixedRootBlock s f d) := by
  unfold FactorFixedRootBlock
  infer_instance

/-- The two descriptions retain precisely the same factor polynomial and its coefficient map. -/
def factorFixedRootBlockEquiv (s : ℕ) (f : Polynomial A) (d : RootHomologyDegrees s) :
    FactorFixedRootBlock s f d ≃ₗ[A] FactorSignedModule d.val.1 d.val.2 f := by
  obtain ⟨⟨q,r⟩,hd⟩ := d
  have hs : s=q+2*r := by omega
  cases hs
  exact LinearEquiv.refl A _

/-- The original coefficient-linear homology equivalence specialized at the factor polynomial. -/
def factorSymmetricHomologyRootEquiv (s : ℕ) (f : Polynomial A) :
    FactorSymmetricHomology s f ≃ₗ[A]
      ⨁ d : RootHomologyDegrees s, FactorSignedModule d.val.1 d.val.2 f := by
  letI : Algebra (Depth.RB s) A := (Collision.coeffHom s f).toRingHom.toAlgebra
  exact (symmetricPowerRootBaseChangeEquiv s A).trans
    (DFinsupp.mapRange.linearEquiv (factorFixedRootBlockEquiv s f))

/-- The literal two-factor root space in the tensor product of factor homologies. -/
abbrev FactorHomologyRootPair (s₁ s₂ : ℕ) (f₁ f₂ : Polynomial A)
    (d : RootHomologyDegrees s₁ × RootHomologyDegrees s₂) :=
  FactorSignedModule d.1.val.1 d.1.val.2 f₁ ⊗[A]
    FactorSignedModule d.2.val.1 d.2.val.2 f₂

/-- The two original factor homologies in their separate root degrees. -/
def factorSymmetricHomologyTensorRootEquiv (s₁ s₂ : ℕ) (f₁ f₂ : Polynomial A) :
    (FactorSymmetricHomology s₁ f₁ ⊗[A] FactorSymmetricHomology s₂ f₂) ≃ₗ[A]
      ⨁ d : RootHomologyDegrees s₁ × RootHomologyDegrees s₂, FactorHomologyRootPair s₁ s₂ f₁ f₂ d := by
  classical
  exact (TensorProduct.congr (factorSymmetricHomologyRootEquiv s₁ f₁)
    (factorSymmetricHomologyRootEquiv s₂ f₂)).trans
      (TensorProduct.directSum A A
        (fun d : RootHomologyDegrees s₁ => FactorSignedModule d.val.1 d.val.2 f₁)
        (fun d : RootHomologyDegrees s₂ => FactorSignedModule d.val.1 d.val.2 f₂))

variable {s₁ s₂ : ℕ} [Algebra (Depth.RB (s₁+s₂)) A]
variable (c : Collision.ChartData (s₁+s₂) s₁ s₂ A)

/-- Reindexing an allocation preserves both concrete factor modules. -/
def rootPairFactorEquiv (d : RootHomologyDegrees s₁ × RootHomologyDegrees s₂) :
    FixedRootOrbitFactor c ((rootDegreeAllocationEquiv s₁ s₂).symm d).1
      ((rootDegreeAllocationEquiv s₁ s₂).symm d).2 ≃ₗ[A]
      FactorHomologyRootPair s₁ s₂ c.f₁ c.f₂ d := by
  change (FactorSignedModule d.1.val.1 d.1.val.2 c.f₁ ⊗[A]
    FactorSignedModule ((d.1.val.1+d.2.val.1)-d.1.val.1)
      ((d.1.val.2+d.2.val.2)-d.1.val.2) c.f₂) ≃ₗ[A] _
  rw [Nat.add_sub_cancel_left,Nat.add_sub_cancel_left]

/-- The complete allocation sum is exactly the pair of output root-degree sums. -/
def fixedRootChartPairsEquiv :
    (⨁ d : RootHomologyDegrees (s₁+s₂),
      (∀ j : OrbitIndex d.val.1 d.val.2 s₁, FixedRootOrbitFactor c d j)) ≃ₗ[A]
      ⨁ d : RootHomologyDegrees s₁ × RootHomologyDegrees s₂, FactorHomologyRootPair s₁ s₂ c.f₁ c.f₂ d := by
  classical
  let e₁ := DFinsupp.mapRange.linearEquiv (fun d : RootHomologyDegrees (s₁+s₂) =>
    (DirectSum.linearEquivFunOnFintype A (OrbitIndex d.val.1 d.val.2 s₁)
      (FixedRootOrbitFactor c d)).symm)
  let e₂ := (DirectSum.sigmaLcurryEquiv A
    (δ := fun (d : RootHomologyDegrees (s₁+s₂)) (j : OrbitIndex d.val.1 d.val.2 s₁) =>
      FixedRootOrbitFactor c d j)).symm
  let e₃ := DirectSum.lequivCongrLeft A
    (M := fun d : RootDegreeAllocation s₁ s₂ => FixedRootOrbitFactor c d.1 d.2)
    (rootDegreeAllocationEquiv s₁ s₂)
  exact ((e₁.trans e₂).trans e₃).trans (DFinsupp.mapRange.linearEquiv (rootPairFactorEquiv c))

/-- Coordinate description of normalized literal root-chart restriction on scalar-extended original homology.
This equivalence is available for proving bijectivity once the original CE chart map is identified by its component diagram. -/
def normalizedHomologyRootChartEquiv :
    (A ⊗[Depth.RB (s₁+s₂)] TotalHomology (symmetricPower (s₁+s₂))) ≃ₗ[A]
      FactorSymmetricHomology s₁ c.f₁ ⊗[A] FactorSymmetricHomology s₂ c.f₂ :=
  ((symmetricPowerRootChartCoordinatesEquiv c rfl).trans (fixedRootChartPairsEquiv c)).trans
    (factorSymmetricHomologyTensorRootEquiv s₁ s₂ c.f₁ c.f₂).symm

end KhanSL2.Macdonald
