module

public import KhanSL2.SymmetricFamily.BaseChangedLabelled
public import KhanSL2.SymmetricFamily.RootAssignmentCanonical
public import KhanSL2.SymmetricFamily.ColorPermutation
public import KhanSL2.SymmetricFamily.TensorPiLeft
public import KhanSL2.Factorization.OrbitStabilizerTensor
public import KhanSL2.Factorization.OrbitStabilizerDecomposition

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-! Exact decomposition and orbit restriction of the actual colored root
families. The component map remains the original root quotient map tensored
with the identity on color tensors. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Factorization

variable (k : ℕ) (A : Type) [CommRing A] [Algebra (Depth.RB k) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB k) A]

/-- The actual colored root-assignment fibre. -/
abbrev ColoredAssignment {r s : ℕ} (c : Collision.ChartData k r s A) (S : Assignment k r) :=
  (RootBase k A ⧸ assignmentFactorIdeal k A c S) ⊗[ℂ] Color k

/-- Split the actual root ring into all quotient components while retaining colors. -/
def coloredAssignmentSplitting {r s : ℕ} (c : Collision.ChartData k r s A) :
    BaseLabelled k A ≃ₗ[A] ∀ S : Assignment k r, ColoredAssignment k A c S :=
  (TensorProduct.AlgebraTensorModule.congr
    (canonicalRootAssignmentSplitting k A c).toLinearEquiv (LinearEquiv.refl ℂ (Color k))).trans
      (tensorPiLeftEquiv ℂ (fun S : Assignment k r =>
        RootBase k A ⧸ assignmentFactorIdeal k A c S) (Color k) A)

@[simp] theorem coloredAssignmentSplitting_tmul {r s : ℕ} (c : Collision.ChartData k r s A)
    (q : RootBase k A) (v : Color k) (S : Assignment k r) :
    coloredAssignmentSplitting k A c (q ⊗ₜ[ℂ] v) S = Ideal.Quotient.mk _ q ⊗ₜ[ℂ] v := by
  simp only [coloredAssignmentSplitting, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    tensorPiLeftEquiv_tmul, AlgEquiv.coe_toLinearEquiv, canonicalRootAssignmentSplitting_apply]

/-- Honest simultaneous transport of the original quotient roots and color slots. -/
def coloredAssignmentTransport {r s : ℕ} (c : Collision.ChartData k r s A) :
    FiberTransport (R := A) (G := Equiv.Perm (Fin k)) (ColoredAssignment k A c) :=
  (rootAssignmentTransport k A c).tensorOver (colorPermutationRepresentation k)

/-- The canonical colored decomposition is equivariant for the actual slot action. -/
theorem coloredAssignmentSplitting_equivariant {r s : ℕ} (c : Collision.ChartData k r s A)
    (σ : Equiv.Perm (Fin k)) (S T : Assignment k r) (h : σ • S = T) (x : BaseLabelled k A) :
    (coloredAssignmentTransport k A c).move σ S T h (coloredAssignmentSplitting k A c x S) =
      coloredAssignmentSplitting k A c (baseLabelledPermute k A σ.symm x) T := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul q v =>
    rw [coloredAssignmentSplitting_tmul, baseLabelledPermute_tmul,
      coloredAssignmentSplitting_tmul]
    change (rootAssignmentTransport k A c).move σ S T h (Ideal.Quotient.mk _ q) ⊗ₜ[ℂ]
      colorPermutationEquiv σ v =
        Ideal.Quotient.mk _ (baseRootPermutation k A σ.symm.symm q) ⊗ₜ[ℂ] colorPermute σ.symm v
    rw [← LinearMap.congr_fun (colorPermutationEquiv_toLinearMap σ) v]
    rfl

/-- Actual root/color invariants restrict exactly to stabilizer invariants in one block. -/
def coloredAssignmentStabilizerEquiv {r s : ℕ} (c : Collision.ChartData k r s A)
    (S₀ : Assignment k r) :
    FiberTransport.fixedVectors (fun σ : Equiv.Perm (Fin k) => baseLabelledPermute k A σ.symm) ≃ₗ[A]
      (coloredAssignmentTransport k A c).stabilizerFixed S₀ :=
  FiberTransport.fixedVectorsEquivStabilizer (coloredAssignmentTransport k A c)
    (fun σ => baseLabelledPermute k A σ.symm) (coloredAssignmentSplitting k A c)
    (coloredAssignmentSplitting_equivariant k A c) S₀
    (fun S => assignment_transitive S₀ S)

end KhanSL2.SymmetricFamily
