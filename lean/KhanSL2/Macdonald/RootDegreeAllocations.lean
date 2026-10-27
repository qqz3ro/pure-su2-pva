module

public import KhanSL2.Macdonald.FixedHomologyRootCoproduct
public import KhanSL2.Factorization.WeightedRootModelOrbits

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace KhanSL2.Macdonald
open Factorization.WeightedRootModel

/-- A fixed input root degree together with an admissible allocation to the first chart factor. -/
abbrev RootDegreeAllocation (s₁ s₂ : ℕ) :=
  Σ d : RootHomologyDegrees (s₁+s₂), OrbitIndex d.val.1 d.val.2 s₁

/-- Retain the two actual odd/even bidegrees selected by an admissible allocation. -/
def rootAllocationPair (s₁ s₂ : ℕ) (x : RootDegreeAllocation s₁ s₂) :
    RootHomologyDegrees s₁ × RootHomologyDegrees s₂ :=
  (⟨x.2.val,by have h := x.2.property.2.2; omega⟩,
    ⟨(x.1.val.1-x.2.val.1,x.1.val.2-x.2.val.2),by
      have h := x.1.property
      have h₁ := x.2.property.1
      have h₂ := x.2.property.2.1
      have hb := x.2.property.2.2
      omega⟩)

/-- A pair of output root degrees determines its original input degree and first-block allocation. -/
def rootPairAllocation (s₁ s₂ : ℕ) (x : RootHomologyDegrees s₁ × RootHomologyDegrees s₂) :
    RootDegreeAllocation s₁ s₂ :=
  ⟨rootDegreeSum x.1 x.2,⟨x.1.val,by
    refine ⟨Nat.le_add_right _ _,Nat.le_add_right _ _,?_⟩
    have h := x.1.property
    omega⟩⟩

/-- The root-factorization indexing is exactly the Cartesian product of the two homology root degrees. -/
def rootDegreeAllocationEquiv (s₁ s₂ : ℕ) :
    RootDegreeAllocation s₁ s₂ ≃ RootHomologyDegrees s₁ × RootHomologyDegrees s₂ where
  toFun := rootAllocationPair s₁ s₂
  invFun := rootPairAllocation s₁ s₂
  left_inv x := by
    apply Sigma.subtype_ext
    · apply Subtype.ext
      apply Prod.ext
      · change x.2.val.1+(x.1.val.1-x.2.val.1)=x.1.val.1
        exact Nat.add_sub_of_le x.2.property.1
      · change x.2.val.2+(x.1.val.2-x.2.val.2)=x.1.val.2
        exact Nat.add_sub_of_le x.2.property.2.1
    · rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Prod.ext <;> simp [rootAllocationPair,rootPairAllocation,rootDegreeSum]

@[simp] theorem rootDegreeAllocationEquiv_symm_first (s₁ s₂ : ℕ)
    (d₁ : RootHomologyDegrees s₁) (d₂ : RootHomologyDegrees s₂) :
    ((rootDegreeAllocationEquiv s₁ s₂).symm (d₁,d₂)).1 = rootDegreeSum d₁ d₂ := rfl

end KhanSL2.Macdonald
