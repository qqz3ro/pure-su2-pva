module

public import KhanSL2.Factorization.WeightedRootModelBlockUniversal

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open Polynomial
open scoped BigOperators TensorProduct
namespace KhanSL2.Factorization.WeightedRootModel
open WeightedRoots

/-- Concatenate odd and even root systems separately, preserving every root label. -/
def appendWeightedRoots {S : Type*} {q₁ q₂ r₁ r₂ : ℕ}
    (x : Fin q₁ ⊕ Fin r₁ → S) (y : Fin q₂ ⊕ Fin r₂ → S) :
    Fin (q₁+q₂) ⊕ Fin (r₁+r₂) → S :=
  Sum.elim (Fin.append (fun i => x (.inl i)) (fun i => y (.inl i)))
    (Fin.append (fun i => x (.inr i)) (fun i => y (.inr i)))

@[simp] theorem appendWeightedRoots_first {S : Type*} {q₁ q₂ r₁ r₂ : ℕ}
    (x : Fin q₁ ⊕ Fin r₁ → S) (y : Fin q₂ ⊕ Fin r₂ → S) :
    appendWeightedRoots x y ∘ firstWeightedInclusion q₁ q₂ r₁ r₂ = x := by
  funext i
  cases i <;> simp [appendWeightedRoots,firstWeightedInclusion]

@[simp] theorem appendWeightedRoots_second {S : Type*} {q₁ q₂ r₁ r₂ : ℕ}
    (x : Fin q₁ ⊕ Fin r₁ → S) (y : Fin q₂ ⊕ Fin r₂ → S) :
    appendWeightedRoots x y ∘ secondWeightedInclusion q₁ q₂ r₁ r₂ = y := by
  funext i
  cases i <;> simp [appendWeightedRoots,secondWeightedInclusion]

variable {q₁ q₂ r₁ r₂ : ℕ} {A : Type} [CommRing A]
variable [Algebra (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) A] [Algebra ℂ A]
variable (c : Collision.ChartData ((q₁+q₂)+2*(r₁+r₂)) (q₁+2*r₁) (q₂+2*r₂) A)

abbrev BlockRootTensor := FactorRoots q₁ r₁ c.f₁ ⊗[A] FactorRoots q₂ r₂ c.f₂

def blockTensorFirstRoot (i : Fin q₁ ⊕ Fin r₁) : BlockRootTensor c :=
  factorRoot q₁ r₁ c.f₁ i ⊗ₜ[A] 1

def blockTensorSecondRoot (i : Fin q₂ ⊕ Fin r₂) : BlockRootTensor c :=
  1 ⊗ₜ[A] factorRoot q₂ r₂ c.f₂ i

theorem blockTensorFirstRoot_product :
    rootProduct (blockTensorFirstRoot c) (rootWeight q₁ r₁) Finset.univ =
      c.f₁.map (algebraMap A (BlockRootTensor c)) := by
  let f : FactorRoots q₁ r₁ c.f₁ →ₐ[A] BlockRootTensor c := Algebra.TensorProduct.includeLeft
  have h := congrArg (Polynomial.map f.toRingHom)
    (factorRoot_product q₁ r₁ c.f₁ c.monic₁ c.degree₁)
  rw [Polynomial.map_map] at h
  have hc : f.toRingHom.comp (algebraMap A (FactorRoots q₁ r₁ c.f₁)) =
      algebraMap A (BlockRootTensor c) := by
    apply RingHom.ext
    intro a
    exact f.commutes a
  rw [hc] at h
  have he (i : Fin q₁ ⊕ Fin r₁) : f.toRingHom (factorRoot q₁ r₁ c.f₁ i) =
      blockTensorFirstRoot c i := Algebra.TensorProduct.includeLeft_apply _
  simpa only [rootProduct_map,he] using h

theorem blockTensorSecondRoot_product :
    rootProduct (blockTensorSecondRoot c) (rootWeight q₂ r₂) Finset.univ =
      c.f₂.map (algebraMap A (BlockRootTensor c)) := by
  let f : FactorRoots q₂ r₂ c.f₂ →ₐ[A] BlockRootTensor c := Algebra.TensorProduct.includeRight
  have h := congrArg (Polynomial.map f.toRingHom)
    (factorRoot_product q₂ r₂ c.f₂ c.monic₂ c.degree₂)
  rw [Polynomial.map_map] at h
  have hc : f.toRingHom.comp (algebraMap A (FactorRoots q₂ r₂ c.f₂)) =
      algebraMap A (BlockRootTensor c) := by
    apply RingHom.ext
    intro a
    exact f.commutes a
  rw [hc] at h
  have he (i : Fin q₂ ⊕ Fin r₂) : f.toRingHom (factorRoot q₂ r₂ c.f₂ i) =
      blockTensorSecondRoot c i := Algebra.TensorProduct.includeRight_apply _
  simpa only [rootProduct_map,he] using h

/-- Literal root restriction to the two smaller weighted root algebras. -/
def blockFactorToTensor : BlockFactor c →ₐ[A] BlockRootTensor c :=
  blockFactorLift c (appendWeightedRoots (blockTensorFirstRoot c) (blockTensorSecondRoot c))
    (by simpa only [appendWeightedRoots_first] using blockTensorFirstRoot_product c)
    (by simpa only [appendWeightedRoots_second] using blockTensorSecondRoot_product c)

@[simp] theorem blockFactorToTensor_firstRoot (i : Fin q₁ ⊕ Fin r₁) :
    blockFactorToTensor c (blockRoot c (firstWeightedInclusion q₁ q₂ r₁ r₂ i)) =
      blockTensorFirstRoot c i := by
  rw [blockFactorToTensor,blockFactorLift_root]
  exact congrFun (appendWeightedRoots_first (blockTensorFirstRoot c) (blockTensorSecondRoot c)) i

@[simp] theorem blockFactorToTensor_secondRoot (i : Fin q₂ ⊕ Fin r₂) :
    blockFactorToTensor c (blockRoot c (secondWeightedInclusion q₁ q₂ r₁ r₂ i)) =
      blockTensorSecondRoot c i := by
  rw [blockFactorToTensor,blockFactorLift_root]
  exact congrFun (appendWeightedRoots_second (blockTensorFirstRoot c) (blockTensorSecondRoot c)) i

def firstFactorToBlock : FactorRoots q₁ r₁ c.f₁ →ₐ[A] BlockFactor c :=
  factorRootsLift q₁ r₁ c.f₁ c.monic₁ c.degree₁
    (blockRoot c ∘ firstWeightedInclusion q₁ q₂ r₁ r₂) (blockRoot_first_product c)

def secondFactorToBlock : FactorRoots q₂ r₂ c.f₂ →ₐ[A] BlockFactor c :=
  factorRootsLift q₂ r₂ c.f₂ c.monic₂ c.degree₂
    (blockRoot c ∘ secondWeightedInclusion q₁ q₂ r₁ r₂) (blockRoot_second_product c)

def blockTensorToFactor : BlockRootTensor c →ₐ[A] BlockFactor c :=
  Algebra.TensorProduct.lift (firstFactorToBlock c) (secondFactorToBlock c)
    (fun _ _ => Commute.all _ _)

@[simp] theorem blockTensorToFactor_firstRoot (i : Fin q₁ ⊕ Fin r₁) :
    blockTensorToFactor c (blockTensorFirstRoot c i) =
      blockRoot c (firstWeightedInclusion q₁ q₂ r₁ r₂ i) := by
  simp [blockTensorToFactor,blockTensorFirstRoot,Algebra.TensorProduct.lift_tmul,firstFactorToBlock]

@[simp] theorem blockTensorToFactor_secondRoot (i : Fin q₂ ⊕ Fin r₂) :
    blockTensorToFactor c (blockTensorSecondRoot c i) =
      blockRoot c (secondWeightedInclusion q₁ q₂ r₁ r₂ i) := by
  simp [blockTensorToFactor,blockTensorSecondRoot,Algebra.TensorProduct.lift_tmul,secondFactorToBlock]

theorem blockTensorToFactor_blockFactorToTensor :
    (blockTensorToFactor c).comp (blockFactorToTensor c) = AlgHom.id A (BlockFactor c) := by
  apply blockFactorAlgHom_ext
  intro i
  have h₁ (j : Fin q₁ ⊕ Fin r₁) :
      blockTensorToFactor c (blockFactorToTensor c
        (blockRoot c (firstWeightedInclusion q₁ q₂ r₁ r₂ j))) =
        blockRoot c (firstWeightedInclusion q₁ q₂ r₁ r₂ j) := by
    rw [blockFactorToTensor_firstRoot,blockTensorToFactor_firstRoot]
  have h₂ (j : Fin q₂ ⊕ Fin r₂) :
      blockTensorToFactor c (blockFactorToTensor c
        (blockRoot c (secondWeightedInclusion q₁ q₂ r₁ r₂ j))) =
        blockRoot c (secondWeightedInclusion q₁ q₂ r₁ r₂ j) := by
    rw [blockFactorToTensor_secondRoot,blockTensorToFactor_secondRoot]
  cases i with
  | inl i => exact Fin.addCases (fun j => h₁ (.inl j)) (fun j => h₂ (.inl j)) i
  | inr i => exact Fin.addCases (fun j => h₁ (.inr j)) (fun j => h₂ (.inr j)) i

theorem blockFactorToTensor_blockTensorToFactor :
    (blockFactorToTensor c).comp (blockTensorToFactor c) = AlgHom.id A (BlockRootTensor c) := by
  apply Algebra.TensorProduct.ext
  · apply factorRootsAlgHom_ext
    intro i
    change blockFactorToTensor c (blockTensorToFactor c (blockTensorFirstRoot c i)) =
      blockTensorFirstRoot c i
    rw [blockTensorToFactor_firstRoot,blockFactorToTensor_firstRoot]
  · apply factorRootsAlgHom_ext
    intro i
    change blockFactorToTensor c (blockTensorToFactor c (blockTensorSecondRoot c i)) =
      blockTensorSecondRoot c i
    rw [blockTensorToFactor_secondRoot,blockFactorToTensor_secondRoot]

/-- The distinguished actual weighted assignment quotient is exactly the tensor
of the two weighted root algebras, over arbitrary possibly nonreduced chart rings. -/
def blockFactorTensorEquiv : BlockFactor c ≃ₐ[A] BlockRootTensor c :=
  AlgEquiv.ofAlgHom (blockFactorToTensor c) (blockTensorToFactor c)
    (blockFactorToTensor_blockTensorToFactor c) (blockTensorToFactor_blockFactorToTensor c)

end KhanSL2.Factorization.WeightedRootModel
