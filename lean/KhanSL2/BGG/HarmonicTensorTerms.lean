module

public import KhanSL2.BGG.EquivariantHarmonicDecomposition
public import KhanSL2.BGG.TermPBWFree
public import Mathlib.LinearAlgebra.TensorProduct.Tower

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct DirectSum
namespace KhanSL2.BGG
namespace PositiveCE

/-- Projection to the chosen standard coefficient representation in degree p. -/
def standardHarmonicProjection (p : ℕ) : Harmonic →ₗ⁅ℂ,G⁆ Coefficient p :=
  (harmonicDegreeStandardEquiv p).toLieModuleHom.comp
    ((DirectSum.lieModuleComponent ℂ ℕ G (fun q => ↥(harmonicDegree q)) p).comp
      harmonicDegreeEquiv.symm.toLieModuleHom)

theorem standardHarmonicEmbedding_injective (p : ℕ) :
    Function.Injective (standardHarmonicEmbedding p) := by
  intro v w h
  apply (harmonicDegreeStandardEquiv p).symm.injective
  exact Subtype.ext h

theorem embedding_projection_eq (p : ℕ) (u : Harmonic) :
    standardHarmonicEmbedding p (standardHarmonicProjection p u) =
      harmonicDegree_isInternal.lieModuleProjection p u := by
  simp only [standardHarmonicEmbedding, standardHarmonicProjection, LieModuleHom.comp_apply,
    LieModuleEquiv.coe_toLieModuleHom, LieModuleEquiv.symm_apply_apply]
  rw [DirectSum.IsInternal.lieModuleProjection_apply]
  have he := congrArg LinearEquiv.symm
    (DirectSum.lieModuleEquivOfIsInternal_toLinearEquiv harmonicDegree harmonicDegree_isInternal)
  exact congrArg (fun z : ⨁ q : ℕ, harmonicDegree q => ((z p : harmonicDegree p) : Harmonic))
    (DFunLike.congr_fun he u)

/-- The coefficient projection and inclusion are inverse on the actual degree-p summand. -/
theorem standardHarmonicEmbedding_projection_of_mem (p : ℕ) (u : Harmonic)
    (hu : u ∈ harmonicDegree p) :
    standardHarmonicEmbedding p (standardHarmonicProjection p u) = u := by
  rw [embedding_projection_eq,
    DirectSum.IsInternal.lieModuleProjection_apply_of_mem harmonicDegree_isInternal p hu]

@[simp] theorem standardHarmonicProjection_embedding (p : ℕ) (v : Coefficient p) :
    standardHarmonicProjection p (standardHarmonicEmbedding p v) = v := by
  apply standardHarmonicEmbedding_injective p
  apply standardHarmonicEmbedding_projection_of_mem
  exact ((harmonicDegreeStandardEquiv p).symm v).property

end PositiveCE

abbrev HarmonicTensor := PositiveEnveloping ⊗[ℂ] PositiveCE.Harmonic

/-- Exterior degree p of the transferred free module. -/
def harmonicTensorDegree (p : ℕ) : Submodule PositiveEnveloping HarmonicTensor :=
  (PositiveCE.harmonicDegree p).toSubmodule.baseChange PositiveEnveloping

/-- The standard p-th coefficient module embedded in the actual harmonic tensor module. -/
def harmonicTensorEmbedding (p : ℕ) :
    PositiveEnveloping ⊗[ℂ] Coefficient p →ₗ[PositiveEnveloping] HarmonicTensor :=
  (PositiveCE.standardHarmonicEmbedding p).toLinearMap.baseChange PositiveEnveloping

/-- Its actual degree projection, extended over the positive enveloping algebra. -/
def harmonicTensorProjection (p : ℕ) :
    HarmonicTensor →ₗ[PositiveEnveloping] PositiveEnveloping ⊗[ℂ] Coefficient p :=
  (PositiveCE.standardHarmonicProjection p).toLinearMap.baseChange PositiveEnveloping

@[simp] theorem harmonicTensorEmbedding_tmul (p : ℕ) (u : PositiveEnveloping) (v : Coefficient p) :
    harmonicTensorEmbedding p (u ⊗ₜ[ℂ] v) = u ⊗ₜ[ℂ] PositiveCE.standardHarmonicEmbedding p v :=
  LinearMap.baseChange_tmul _ _ _

@[simp] theorem harmonicTensorProjection_tmul (p : ℕ) (u : PositiveEnveloping) (v : PositiveCE.Harmonic) :
    harmonicTensorProjection p (u ⊗ₜ[ℂ] v) = u ⊗ₜ[ℂ] PositiveCE.standardHarmonicProjection p v :=
  LinearMap.baseChange_tmul _ _ _

@[simp] theorem harmonicTensorProjection_embedding (p : ℕ)
    (x : PositiveEnveloping ⊗[ℂ] Coefficient p) :
    harmonicTensorProjection p (harmonicTensorEmbedding p x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul u v => simp only [harmonicTensorEmbedding_tmul, harmonicTensorProjection_tmul,
      PositiveCE.standardHarmonicProjection_embedding]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem harmonicTensorEmbedding_mem (p : ℕ) (x : PositiveEnveloping ⊗[ℂ] Coefficient p) :
    harmonicTensorEmbedding p x ∈ harmonicTensorDegree p := by
  induction x using TensorProduct.inductionOn with
  | tmul u v =>
    rw [harmonicTensorEmbedding_tmul]
    apply Submodule.tmul_mem_baseChange_of_mem
    exact ((PositiveCE.harmonicDegreeStandardEquiv p).symm v).property
  | add x y hx hy => rw [map_add]; exact (harmonicTensorDegree p).add_mem hx hy

/-- On a homogeneous harmonic tensor, re-including its coefficient projection is identity. -/
theorem harmonicTensorEmbedding_projection_of_mem (p : ℕ) (x : HarmonicTensor)
    (hx : x ∈ harmonicTensorDegree p) :
    harmonicTensorEmbedding p (harmonicTensorProjection p x) = x := by
  obtain ⟨y, rfl⟩ := Submodule.toBaseChange_surjective' PositiveEnveloping
    (PositiveCE.harmonicDegree p).toSubmodule hx
  clear hx
  induction y using TensorProduct.inductionOn with
  | tmul u v =>
    rw [Submodule.coe_toBaseChange_tmul, harmonicTensorProjection_tmul,
      harmonicTensorEmbedding_tmul, PositiveCE.standardHarmonicEmbedding_projection_of_mem p v v.property]
  | add x y hx hy =>
    simp only [map_add, Submodule.coe_add, hx, hy]

/-- The actual relative induced term embeds into the transferred harmonic module. -/
def termHarmonicEmbedding (p : ℕ) : Term p →ₗ[PositiveEnveloping] HarmonicTensor :=
  (harmonicTensorEmbedding p).comp (positiveTensorModuleEquivTerm p).symm.toLinearMap

/-- The corresponding projection has the actual relative induced term as codomain. -/
def termHarmonicProjection (p : ℕ) : HarmonicTensor →ₗ[PositiveEnveloping] Term p :=
  (positiveTensorModuleEquivTerm p).toLinearMap.comp (harmonicTensorProjection p)

@[simp] theorem termHarmonicProjection_embedding (p : ℕ) (x : Term p) :
    termHarmonicProjection p (termHarmonicEmbedding p x) = x := by
  simp only [termHarmonicProjection, termHarmonicEmbedding, LinearMap.comp_apply,
    LinearEquiv.coe_coe, harmonicTensorProjection_embedding, LinearEquiv.apply_symm_apply]

theorem termHarmonicEmbedding_mem (p : ℕ) (x : Term p) :
    termHarmonicEmbedding p x ∈ harmonicTensorDegree p := harmonicTensorEmbedding_mem p _

theorem termHarmonicEmbedding_projection_of_mem (p : ℕ) (x : HarmonicTensor)
    (hx : x ∈ harmonicTensorDegree p) :
    termHarmonicEmbedding p (termHarmonicProjection p x) = x := by
  simp only [termHarmonicProjection, termHarmonicEmbedding, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact harmonicTensorEmbedding_projection_of_mem p x hx

end KhanSL2.BGG