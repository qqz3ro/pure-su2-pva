module

public import KhanSL2.BGG.RelativeCochainsDegree

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Degree-p harmonic cochains are the actual constant-equivariant maps from V(2p). -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.BGG.PositiveCE

/-- The standard coefficient projection annihilates each different harmonic degree. -/
theorem standardHarmonicProjection_eq_zero_of_mem {p q : ℕ} (hqp : q ≠ p)
    (u : Harmonic) (hu : u ∈ harmonicDegree q) : standardHarmonicProjection p u = 0 := by
  apply standardHarmonicEmbedding_injective p
  rw [map_zero, embedding_projection_eq]
  exact harmonicDegree_isInternal.lieModuleProjection_apply_of_ne hqp ⟨u,hu⟩

end KhanSL2.BGG.PositiveCE

namespace KhanSL2.BGG.RelativeCochains
open scoped RelativeCochains
variable (M : Type*) [AddCommGroup M] [Module ℂ M]
  [Module Enveloping M] [IsScalarTower ℂ Enveloping M]
variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule G V] [LieModule ℂ G V]
  [AddCommGroup W] [Module ℂ W] [LieRingModule G W] [LieModule ℂ G W]

/-- Precompose ordinary relative coefficient maps by an actual constant Lie-module map. -/
def coefficientPrecompose (F : V →ₗ⁅ℂ,G⁆ W) :
    coefficientHom M W →ₗ[ℂ] coefficientHom M V where
  toFun f := ⟨f.val.comp F.toLinearMap, by
    intro x v
    change f.val (F ⁅x,v⁆) = _
    rw [F.map_lie, f.property]
    rfl⟩
  map_add' f g := by apply Subtype.ext; apply LinearMap.ext; intro v; rfl
  map_smul' r f := by apply Subtype.ext; apply LinearMap.ext; intro v; rfl

omit [LieModule ℂ G V] [LieModule ℂ G W] in
@[simp] theorem coefficientPrecompose_apply (F : V →ₗ⁅ℂ,G⁆ W)
    (f : coefficientHom M W) (v : V) :
    (coefficientPrecompose M F f).val v = f.val (F v) := rfl

/-- Extract the actual coefficient map on the chosen standard harmonic summand. -/
def harmonicToCoefficient (p : ℕ) : harmonicDegree M p →ₗ[ℂ] coefficientHom M (Coefficient p) :=
  (coefficientPrecompose M (PositiveCE.standardHarmonicEmbedding p)).comp
    ((tensorHomEquiv M PositiveCE.Harmonic).toLinearMap.comp (harmonicDegree M p).subtype)

@[simp] theorem harmonicToCoefficient_apply (p : ℕ) (f : harmonicDegree M p) (v : Coefficient p) :
    (harmonicToCoefficient M p f).val v =
      f.val.val (1 ⊗ₜ[ℂ] PositiveCE.standardHarmonicEmbedding p v) := rfl

/-- Extend a coefficient map by the actual harmonic degree projection and positive action. -/
def coefficientToHarmonic (p : ℕ) : coefficientHom M (Coefficient p) →ₗ[ℂ] harmonicDegree M p where
  toFun f := ⟨(tensorHomEquiv M PositiveCE.Harmonic).symm
      (coefficientPrecompose M (PositiveCE.standardHarmonicProjection p) f), by
    intro q hq u hu
    obtain ⟨v,rfl⟩ := Submodule.toBaseChange_surjective' PositiveEnveloping
      (PositiveCE.harmonicDegree q).toSubmodule hu
    clear hu
    induction v using TensorProduct.inductionOn with
    | tmul a w =>
      rw [Submodule.coe_toBaseChange_tmul, tensorHomEquiv_symm_tmul,
        coefficientPrecompose_apply, PositiveCE.standardHarmonicProjection_eq_zero_of_mem hq _ w.property,
        map_zero, smul_zero]
    | add v w hv hw => simp only [map_add, Submodule.coe_add, hv, hw, add_zero]⟩
  map_add' f g := by
    apply Subtype.ext
    let e := (tensorHomEquiv M PositiveCE.Harmonic).symm
    let F := coefficientPrecompose M (PositiveCE.standardHarmonicProjection p)
    change e (F (f+g)) = e (F f) + e (F g)
    exact (congrArg e (F.map_add f g)).trans (e.map_add (F f) (F g))
  map_smul' r f := by
    apply Subtype.ext
    let e := (tensorHomEquiv M PositiveCE.Harmonic).symm
    let F := coefficientPrecompose M (PositiveCE.standardHarmonicProjection p)
    change e (F (r • f)) = r • e (F f)
    exact (congrArg e (F.map_smul r f)).trans (e.map_smul r (F f))
@[simp] theorem coefficientToHarmonic_tmul (p : ℕ) (f : coefficientHom M (Coefficient p))
    (a : PositiveEnveloping) (u : PositiveCE.Harmonic) :
    (coefficientToHarmonic M p f).val.val (a ⊗ₜ[ℂ] u) =
      positiveFactor a • f.val (PositiveCE.standardHarmonicProjection p u) := rfl

/-- A cochain supported in degree p is determined by its value on the actual p-th summand. -/
theorem harmonic_cochain_projection (p : ℕ) (f : harmonicDegree M p) (u : PositiveCE.Harmonic) :
    f.val.val (1 ⊗ₜ[ℂ] PositiveCE.standardHarmonicEmbedding p
      (PositiveCE.standardHarmonicProjection p u)) = f.val.val (1 ⊗ₜ[ℂ] u) := by
  let g := (tensorHomEquiv M PositiveCE.Harmonic f.val).val
  let e := (PositiveCE.standardHarmonicEmbedding p).toLinearMap.comp
    (PositiveCE.standardHarmonicProjection p).toLinearMap
  let F := g.comp e - g
  have hk : (⊤ : Submodule ℂ PositiveCE.Harmonic) ≤ LinearMap.ker F := by
    rw [← PositiveCE.harmonicDegree_isInternal.submodule_iSup_eq_top]
    apply iSup_le
    intro q w hw
    change g (e w) - g w = 0
    by_cases hq : q=p
    · subst q
      change g (PositiveCE.standardHarmonicEmbedding p (PositiveCE.standardHarmonicProjection p w)) - g w = 0
      rw [PositiveCE.standardHarmonicEmbedding_projection_of_mem p w hw, sub_self]
    · change g (PositiveCE.standardHarmonicEmbedding p (PositiveCE.standardHarmonicProjection p w)) - g w = 0
      rw [PositiveCE.standardHarmonicProjection_eq_zero_of_mem hq w hw, map_zero, map_zero]
      have hf := f.property q hq (1 ⊗ₜ[ℂ] w) (Submodule.tmul_mem_baseChange_of_mem 1 hw)
      change g w = 0 at hf
      rw [hf, sub_self]
  exact sub_eq_zero.mp (hk (Submodule.mem_top : u ∈ (⊤ : Submodule ℂ PositiveCE.Harmonic)))

set_option maxHeartbeats 800000 in
/-- Actual homogeneous harmonic cochains identify with constant-equivariant maps from V(2p). -/
def harmonicCoefficientEquiv (p : ℕ) : harmonicDegree M p ≃ₗ[ℂ] coefficientHom M (Coefficient p) where
  toLinearMap := harmonicToCoefficient M p
  invFun := coefficientToHarmonic M p
  left_inv f := by
    apply Subtype.ext
    apply tensorHom_ext M
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a u =>
      change (coefficientToHarmonic M p (harmonicToCoefficient M p f)).val.val (a ⊗ₜ[ℂ] u) = f.val.val (a ⊗ₜ[ℂ] u)
      rw [coefficientToHarmonic_tmul, harmonicToCoefficient_apply, harmonic_cochain_projection]
      change a • f.val.val (1 ⊗ₜ[ℂ] u) = f.val.val (a ⊗ₜ[ℂ] u)
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
        (f.val.val.map_smul a (1 ⊗ₜ[ℂ] u)).symm
    | add t s ht hs => simp only [map_add, ht, hs]
  right_inv f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change (harmonicToCoefficient M p (coefficientToHarmonic M p f)).val v = f.val v
    rw [harmonicToCoefficient_apply, coefficientToHarmonic_tmul,
      PositiveCE.standardHarmonicProjection_embedding, map_one, one_smul]

end KhanSL2.BGG.RelativeCochains
