module

public import KhanSL2.SymmetricFamily.RootBlockUniversal

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-! The distinguished actual root-assignment quotient is the tensor product of
the two smaller labelled-root algebras. Both directions are explicit on roots. -/

noncomputable section
open Polynomial
open scoped BigOperators TensorProduct
namespace KhanSL2.SymmetricFamily

variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]
variable [Algebra ℂ A]

/-- The two genuine smaller root algebras over the chart's prescribed coefficient maps. -/
abbrev BlockRootTensor (c : Collision.ChartData (r+s) r s A) :=
  FactorRoots r c.f₁ ⊗[A] FactorRoots s c.f₂

/-- Ordered roots from the first tensor factor. -/
def blockTensorLeftRoot (c : Collision.ChartData (r+s) r s A) (i : Fin r) : BlockRootTensor c :=
  (factorRoot r c.f₁ i) ⊗ₜ[A] 1

/-- Ordered roots from the second tensor factor. -/
def blockTensorRightRoot (c : Collision.ChartData (r+s) r s A) (i : Fin s) : BlockRootTensor c :=
  1 ⊗ₜ[A] (factorRoot s c.f₂ i)

theorem blockTensorLeftRoot_product (c : Collision.ChartData (r+s) r s A) :
    ∏ i : Fin r, (Polynomial.X - Polynomial.C (blockTensorLeftRoot c i)) =
      c.f₁.map (algebraMap A (BlockRootTensor c)) := by
  let f : FactorRoots r c.f₁ →ₐ[A] BlockRootTensor c := Algebra.TensorProduct.includeLeft
  have h := congrArg (Polynomial.map f.toRingHom)
    (factorRoot_product r c.f₁ c.monic₁ c.degree₁)
  rw [Polynomial.map_map] at h
  have hc : f.toRingHom.comp (algebraMap A (FactorRoots r c.f₁)) =
      algebraMap A (BlockRootTensor c) := by
    apply RingHom.ext
    intro a
    exact f.commutes a
  rw [hc] at h
  have he (i : Fin r) : f.toRingHom (factorRoot r c.f₁ i) = blockTensorLeftRoot c i :=
    Algebra.TensorProduct.includeLeft_apply _
  simpa only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, he] using h

theorem blockTensorRightRoot_product (c : Collision.ChartData (r+s) r s A) :
    ∏ i : Fin s, (Polynomial.X - Polynomial.C (blockTensorRightRoot c i)) =
      c.f₂.map (algebraMap A (BlockRootTensor c)) := by
  let f : FactorRoots s c.f₂ →ₐ[A] BlockRootTensor c := Algebra.TensorProduct.includeRight
  have h := congrArg (Polynomial.map f.toRingHom)
    (factorRoot_product s c.f₂ c.monic₂ c.degree₂)
  rw [Polynomial.map_map] at h
  have hc : f.toRingHom.comp (algebraMap A (FactorRoots s c.f₂)) =
      algebraMap A (BlockRootTensor c) := by
    apply RingHom.ext
    intro a
    exact f.commutes a
  rw [hc] at h
  have he (i : Fin s) : f.toRingHom (factorRoot s c.f₂ i) = blockTensorRightRoot c i :=
    Algebra.TensorProduct.includeRight_apply _
  simpa only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, he] using h

/-- The root-assignment quotient maps to the two smaller labelled-root families. -/
def blockFactorToTensor (c : Collision.ChartData (r+s) r s A) :
    BlockFactor c →ₐ[A] BlockRootTensor c :=
  blockFactorLift c (Fin.append (blockTensorLeftRoot c) (blockTensorRightRoot c))
    (by simpa only [Fin.append_left] using blockTensorLeftRoot_product c)
    (by simpa only [Fin.append_right] using blockTensorRightRoot_product c)

@[simp] theorem blockFactorToTensor_leftRoot (c : Collision.ChartData (r+s) r s A) (i : Fin r) :
    blockFactorToTensor c (blockRoot c (Fin.castAdd s i)) = blockTensorLeftRoot c i := by
  simp only [blockFactorToTensor, blockFactorLift_root, Fin.append_left]

@[simp] theorem blockFactorToTensor_rightRoot (c : Collision.ChartData (r+s) r s A) (i : Fin s) :
    blockFactorToTensor c (blockRoot c (Fin.natAdd r i)) = blockTensorRightRoot c i := by
  simp only [blockFactorToTensor, blockFactorLift_root, Fin.append_right]

/-- The first smaller root family maps to its original block of quotient roots. -/
def leftFactorToBlock (c : Collision.ChartData (r+s) r s A) :
    FactorRoots r c.f₁ →ₐ[A] BlockFactor c :=
  factorRootsLift r c.f₁ c.monic₁ c.degree₁
    (fun i => blockRoot c (Fin.castAdd s i)) (blockRoot_left_product c)

/-- The second smaller root family maps to its original block of quotient roots. -/
def rightFactorToBlock (c : Collision.ChartData (r+s) r s A) :
    FactorRoots s c.f₂ →ₐ[A] BlockFactor c :=
  factorRootsLift s c.f₂ c.monic₂ c.degree₂
    (fun i => blockRoot c (Fin.natAdd r i)) (blockRoot_right_product c)

/-- Multiplying the two root-system maps gives the inverse map. -/
def blockTensorToFactor (c : Collision.ChartData (r+s) r s A) :
    BlockRootTensor c →ₐ[A] BlockFactor c :=
  Algebra.TensorProduct.lift (leftFactorToBlock c) (rightFactorToBlock c)
    (fun _ _ => Commute.all _ _)

@[simp] theorem blockTensorToFactor_leftRoot (c : Collision.ChartData (r+s) r s A) (i : Fin r) :
    blockTensorToFactor c (blockTensorLeftRoot c i) = blockRoot c (Fin.castAdd s i) := by
  simp [blockTensorToFactor, blockTensorLeftRoot, Algebra.TensorProduct.lift_tmul,
    leftFactorToBlock]

@[simp] theorem blockTensorToFactor_rightRoot (c : Collision.ChartData (r+s) r s A) (i : Fin s) :
    blockTensorToFactor c (blockTensorRightRoot c i) = blockRoot c (Fin.natAdd r i) := by
  simp [blockTensorToFactor, blockTensorRightRoot, Algebra.TensorProduct.lift_tmul,
    rightFactorToBlock]

theorem blockTensorToFactor_blockFactorToTensor (c : Collision.ChartData (r+s) r s A) :
    (blockTensorToFactor c).comp (blockFactorToTensor c) = AlgHom.id A (BlockFactor c) := by
  apply blockFactorAlgHom_ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [AlgHom.comp_apply, blockFactorToTensor_leftRoot, blockFactorToTensor_rightRoot,
      blockTensorToFactor_leftRoot, blockTensorToFactor_rightRoot, AlgHom.id_apply]

theorem blockFactorToTensor_blockTensorToFactor (c : Collision.ChartData (r+s) r s A) :
    (blockFactorToTensor c).comp (blockTensorToFactor c) = AlgHom.id A (BlockRootTensor c) := by
  apply Algebra.TensorProduct.ext
  · apply factorRootsAlgHom_ext
    intro i
    change blockFactorToTensor c (blockTensorToFactor c (blockTensorLeftRoot c i)) =
      blockTensorLeftRoot c i
    rw [blockTensorToFactor_leftRoot, blockFactorToTensor_leftRoot]
  · apply factorRootsAlgHom_ext
    intro i
    change blockFactorToTensor c (blockTensorToFactor c (blockTensorRightRoot c i)) =
      blockTensorRightRoot c i
    rw [blockTensorToFactor_rightRoot, blockFactorToTensor_rightRoot]

/-- Exact first-block algebra identification, valid over arbitrary chart rings. -/
def blockFactorTensorEquiv (c : Collision.ChartData (r+s) r s A) :
    BlockFactor c ≃ₐ[A] BlockRootTensor c :=
  AlgEquiv.ofAlgHom (blockFactorToTensor c) (blockTensorToFactor c)
    (blockFactorToTensor_blockTensorToFactor c) (blockTensorToFactor_blockFactorToTensor c)

end KhanSL2.SymmetricFamily
