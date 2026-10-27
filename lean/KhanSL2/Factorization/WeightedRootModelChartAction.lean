module

public import KhanSL2.Factorization.WeightedRootModelAssignments
public import KhanSL2.Factorization.WeightedRootModelInvariants
public import KhanSL2.Factorization.OrbitStabilizerQuotient
public import KhanSL2.Factorization.OrbitStabilizerDecomposition
public import KhanSL2.SymmetricFamily.RootPermutation

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped TensorProduct BigOperators
namespace KhanSL2.Factorization.WeightedRootModel
open WeightedRoots

variable (q r : ℕ) (A : Type) [CommRing A] [Algebra (Depth.RB (q+2*r)) A]

/-- The actual weighted block permutation over the chart coefficient algebra. -/
def baseBlockAutomorphism (g : BlockGroup q r) : WeightedBase q r A ≃ₐ[A] WeightedBase q r A :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) (blockRootAutomorphism g)

@[simp] theorem baseBlockAutomorphism_tmul (g : BlockGroup q r) (a : A) (p : LabelledWeightedRing q r) :
    baseBlockAutomorphism q r A g (a ⊗ₜ[Depth.RB (q+2*r)] p) =
      a ⊗ₜ[Depth.RB (q+2*r)] blockRootAutomorphism g p := by
  simp [baseBlockAutomorphism]

@[simp] theorem baseBlockAutomorphism_root (g : BlockGroup q r) (i : Fin q ⊕ Fin r) :
    baseBlockAutomorphism q r A g (baseRoot q r A i) = baseRoot q r A (blockPermutation g i) := by
  change baseBlockAutomorphism q r A g
    (1 ⊗ₜ[Depth.RB (q+2*r)] (show LabelledWeightedRing q r from MvPolynomial.X i)) = _
  rw [baseBlockAutomorphism_tmul,blockRootAutomorphism_apply,MvPolynomial.rename_X]
  rfl

def baseBlockAction : BlockGroup q r →* (WeightedBase q r A ≃ₐ[A] WeightedBase q r A) where
  toFun := baseBlockAutomorphism q r A
  map_one' := by
    apply AlgEquiv.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a p =>
      rw [baseBlockAutomorphism_tmul]
      have h : blockRootAutomorphism (1 : BlockGroup q r) p = p :=
        congrArg (fun e => e p) (blockRootAction q r).map_one
      rw [h]
      rfl
    | add x y hx hy => simp only [map_add,hx,hy]
  map_mul' g h := by
    apply AlgEquiv.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a p =>
      change baseBlockAutomorphism q r A (g*h) (a ⊗ₜ[Depth.RB (q+2*r)] p) =
        baseBlockAutomorphism q r A g (baseBlockAutomorphism q r A h (a ⊗ₜ[Depth.RB (q+2*r)] p))
      rw [baseBlockAutomorphism_tmul,baseBlockAutomorphism_tmul,baseBlockAutomorphism_tmul]
      exact congrArg (fun z => a ⊗ₜ[Depth.RB (q+2*r)] z)
        (congrArg (fun e => e p) ((blockRootAction q r).map_mul g h))
    | add x y hx hy => simp only [map_add,hx,hy]

theorem baseBlock_rootProduct (g : BlockGroup q r) (S : Finset (Fin q ⊕ Fin r)) :
    (rootProduct (baseRoot q r A) (rootWeight q r) S).map (baseBlockAutomorphism q r A g).toRingHom =
      rootProduct (baseRoot q r A) (rootWeight q r) (S.map (blockPermutation g).toEmbedding) := by
  simp only [rootProduct,Polynomial.map_prod,Polynomial.map_pow,Polynomial.map_sub,
    Polynomial.map_X,Polynomial.map_C,Finset.prod_map,Equiv.coe_toEmbedding,
    rootWeight_blockPermutation]
  apply Finset.prod_congr rfl
  intro i _
  rw [show (baseBlockAutomorphism q r A g).toRingHom (baseRoot q r A i) =
    baseRoot q r A (blockPermutation g i) from baseBlockAutomorphism_root q r A g i]

theorem baseBlock_factor (g : BlockGroup q r) (f : A[X]) :
    (f.map (algebraMap A (WeightedBase q r A))).map (baseBlockAutomorphism q r A g).toRingHom =
      f.map (algebraMap A (WeightedBase q r A)) := by
  rw [Polynomial.map_map]
  congr 1
  apply RingHom.ext
  intro a
  exact (baseBlockAutomorphism q r A g).commutes a

private theorem map_compl (g : BlockGroup q r) (S : Finset (Fin q ⊕ Fin r)) :
    Sᶜ.map (blockPermutation g).toEmbedding = (S.map (blockPermutation g).toEmbedding)ᶜ := by
  ext i
  simp only [Finset.mem_map_equiv,Finset.mem_compl]

def assignmentIdeal {b₁ b₂ : ℕ} (c : Collision.ChartData (q+2*r) b₁ b₂ A)
    (σ : WeightedAssignment q r b₁) : Ideal (WeightedBase q r A) :=
  factorIdeal (c.f₁.map (algebraMap A (WeightedBase q r A)))
    (c.f₂.map (algebraMap A (WeightedBase q r A))) (baseRoot q r A) (rootWeight q r) (selected σ.val)

theorem baseBlock_assignmentIdeal {b₁ b₂ : ℕ} (c : Collision.ChartData (q+2*r) b₁ b₂ A)
    (g : BlockGroup q r) (σ : WeightedAssignment q r b₁) :
    Ideal.map (baseBlockAction q r A g).toRingHom (assignmentIdeal q r A c σ) =
      assignmentIdeal q r A c (g • σ) := by
  change Ideal.map (baseBlockAutomorphism q r A g).toRingHom _ = _
  simp only [assignmentIdeal,factorIdeal,Ideal.map_sup,SymmetricFamily.map_coefficientIdeal,
    Polynomial.map_sub,baseBlock_rootProduct,baseBlock_factor,map_compl]
  rw [show selected (g • σ).val = (selected σ.val).map (blockPermutation g).toEmbedding from
    selected_assignmentRelabel g σ]

/-- Actual coefficient-linear transport between the weighted factor quotient algebras. -/
def assignmentTransport {b₁ b₂ : ℕ} (c : Collision.ChartData (q+2*r) b₁ b₂ A) :
    FiberTransport (R:=A) (G:=BlockGroup q r) (fun σ => AssignmentRing q r A c σ) :=
  FiberTransport.quotients (baseBlockAction q r A) (assignmentIdeal q r A c)
    (baseBlock_assignmentIdeal q r A c)

def baseBlockSign : BlockGroup q r →* Aˣ :=
  (Units.map (algebraMap (Depth.RB (q+2*r)) A)).comp (blockSign q r)

/-- The sign twist on the odd labels of every actual assignment quotient. -/
def signedAssignmentTransport {b₁ b₂ : ℕ} (c : Collision.ChartData (q+2*r) b₁ b₂ A) :
    FiberTransport (R:=A) (G:=BlockGroup q r) (fun σ => AssignmentRing q r A c σ) :=
  (assignmentTransport q r A c).twist (baseBlockSign q r A)

/-- The signed operator after coefficient base change is the actual signed chart permutation. -/
theorem signedBlock_baseChange_apply (g : BlockGroup q r) (x : WeightedBase q r A) :
    (signedBlockOperator g).baseChange A x =
      (baseBlockSign q r A g : A) • baseBlockAutomorphism q r A g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    rw [LinearMap.baseChange_tmul,baseBlockAutomorphism_tmul]
    change a ⊗ₜ[Depth.RB (q+2*r)] ((blockSign q r g : Depth.RB (q+2*r)) • blockRootAutomorphism g p) =
      algebraMap (Depth.RB (q+2*r)) A (blockSign q r g) •
        (a ⊗ₜ[Depth.RB (q+2*r)] blockRootAutomorphism g p)
    rw [TensorProduct.tmul_smul,← IsScalarTower.algebraMap_smul A (blockSign q r g : Depth.RB (q+2*r))]
  | add x y hx hy => simp only [map_add,hx,hy,smul_add]

/-- Signed invariants of the actual chart algebra are the actual invariant
sections of its weighted quotient decomposition, with literal component maps. -/
def signedInvariantSectionsEquiv {b₁ b₂ : ℕ} (c : Collision.ChartData (q+2*r) b₁ b₂ A) :
    (A ⊗[Depth.RB (q+2*r)] signedInvariantModule q r) ≃ₗ[A]
      (signedAssignmentTransport q r A c).invariantSections := by
  refine (signedInvariantBaseChangeEquiv q r A).trans
    (FiberTransport.fixedVectorsEquivSections (signedAssignmentTransport q r A c)
      (fun g => (signedBlockOperator g).baseChange A) (assignmentSplitting q r A c).toLinearEquiv ?_)
  intro g i j h x
  change (baseBlockSign q r A g : A) • Ideal.Quotient.mk (assignmentIdeal q r A c j)
      (baseBlockAutomorphism q r A g x) =
    Ideal.Quotient.mk (assignmentIdeal q r A c j) ((signedBlockOperator g).baseChange A x)
  rw [signedBlock_baseChange_apply]
  exact ((Ideal.Quotient.mkₐ A (assignmentIdeal q r A c j)).toLinearMap.map_smul _ _).symm

end KhanSL2.Factorization.WeightedRootModel



