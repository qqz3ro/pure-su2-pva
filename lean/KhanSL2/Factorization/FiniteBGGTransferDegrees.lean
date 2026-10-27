module

public import KhanSL2.Factorization.FiniteBGGTransferContraction

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
open CategoryTheory
namespace KhanSL2.Factorization.BGGTransfer
open BGG BGGBridge SymmetricFamily

theorem lTensor_mem_tensorLeft {U V : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ U) (f : Module.End ℂ V)
    {z : U ⊗[ℂ] V} (hz : z ∈ tensorLeft P) : LinearMap.lTensor U f z ∈ tensorLeft P := by
  obtain ⟨w,rfl⟩ := hz
  refine ⟨LinearMap.lTensor P f w,?_⟩
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y => rfl

variable (R : Type) [CommRing R] [Algebra ℂ R]
variable (M : Type) [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M] [LieRingModule Current M] [LieModule ℂ Current M]
  [CoefficientLinearCurrent R M]
attribute [local instance] harmonicModule coefficientChainModule coefficientDegreeModule

/-- The actual exterior-degree harmonic group with its original R action. -/
def harmonicDegree (j : ℕ) : Submodule R (HarmonicQuotient M) where
  carrier := (tensorLeft (N:=M) (degH j)).map (relH M).mkQ
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  smul_mem' r z hz := by
    obtain ⟨w,hw,rfl⟩ := hz
    exact ⟨harmonicScalarRaw R M r w,
      lTensor_mem_tensorLeft (degH j) (coefficientScalarLieHom R M r).toLinearMap hw,rfl⟩

/-- Degreewise inclusion is the actual BGG contraction inclusion. -/
def inclDegree (j : ℕ) : harmonicDegree R M j →ₗ[R] degree M j where
  toFun z := ⟨(qcN M).incl z.val,by
    obtain ⟨w,hw,hz⟩ := z.property
    rw [← hz]
    exact ⟨(cN M).incl w,incl_mem_degree M hw,rfl⟩⟩
  map_add' z w := Subtype.ext ((qcN M).incl.map_add z.val w.val)
  map_smul' r z := Subtype.ext (incl_smul R M r z.val)

/-- Degreewise projection is the actual BGG contraction projection. -/
def projDegree (j : ℕ) : degree M j →ₗ[R] harmonicDegree R M j where
  toFun z := ⟨(qcN M).proj z.val,by
    obtain ⟨w,hw,hz⟩ := z.property
    rw [← hz]
    exact ⟨(cN M).proj w,proj_mem_degree M hw,rfl⟩⟩
  map_add' z w := Subtype.ext ((qcN M).proj.map_add z.val w.val)
  map_smul' r z := Subtype.ext (proj_smul R M r z.val)

/-- The actual contracting homotopy raises the unchanged CE exterior degree. -/
def homotopyDegree (j : ℕ) : degree M j →ₗ[R] degree M (j+1) where
  toFun z := ⟨(qcN M).homotopy z.val,by
    obtain ⟨w,hw,hz⟩ := z.property
    rw [← hz]
    exact ⟨(cN M).homotopy w,homotopy_mem_degree M hw,rfl⟩⟩
  map_add' z w := Subtype.ext ((qcN M).homotopy.map_add z.val w.val)
  map_smul' r z := Subtype.ext (homotopy_smul R M r z.val)

def harmonicDegreeDifferential (j : ℕ) : harmonicDegree R M (j+1) →ₗ[R] harmonicDegree R M j where
  toFun z := ⟨dHq M z.val,by
    obtain ⟨w,hw,hz⟩ := z.property
    rw [← hz]
    exact ⟨dH M w,dH_mem_degree M hw,rfl⟩⟩
  map_add' z w := Subtype.ext ((dHq M).map_add z.val w.val)
  map_smul' r z := Subtype.ext (harmonicDifferential_smul R M r z.val)

/-- The same coefficient BGG differential, with genuine exterior degree terms. -/
def harmonicComplex : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun j => ModuleCat.of R (harmonicDegree R M j))
    (fun j => ModuleCat.ofHom (harmonicDegreeDifferential R M j)) (fun _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      exact LinearMap.congr_fun ((qcN M).dN_comp_dN_eq_zero (differential_comp_self M)) z.val)

@[simp] theorem harmonicComplex_d (j : ℕ) :
    (harmonicComplex R M).d (j+1) j = ModuleCat.ofHom (harmonicDegreeDifferential R M j) := by
  simp only [harmonicComplex,ChainComplex.of,ChainComplex.of_d]

/-- Inclusion of the actual coefficient BGG complex into the actual relative CE complex. -/
def inclComplex : harmonicComplex R M ⟶ coefficientRelativeComplex R M :=
  ChainComplex.ofHom (fun j => ModuleCat.ofHom (inclDegree R M j)) (fun j => by
    rw [harmonicComplex_d,coefficientRelativeComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact LinearMap.congr_fun (qcN M).dM_comp_incl z.val)

/-- Projection from the actual relative CE complex onto its coefficient BGG model. -/
def projComplex : coefficientRelativeComplex R M ⟶ harmonicComplex R M :=
  ChainComplex.ofHom (fun j => ModuleCat.ofHom (projDegree R M j)) (fun j => by
    rw [harmonicComplex_d,coefficientRelativeComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact (LinearMap.congr_fun (qcN M).proj_comp_dM z.val).symm)

end KhanSL2.Factorization.BGGTransfer
