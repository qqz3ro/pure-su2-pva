module

public import KhanSL2.BGGBridge.CoefficientWeights
public import KhanSL2.BGGBridge.CoefficientProjection
public import KhanSL2.BGGBridge.TensorCoinvariants

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-!
# The actual BGG coefficient terms vanish above coefficient degree

A coefficient-degree-B exterior monomial has Cartan weights between -2B
and 2B. For p>B the operator H-2p is invertible on that coefficient degree.
The Cartan relation kills tensors with the bottom vector of V(2p), and
raising successively kills the other standard basis tensors. Projecting
the actual harmonic window to coefficient degree B completes the proof.
-/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.BGGBridge
open KhanSL2.BGG KhanSL2.Current

/-- The coefficient-number operator commutes with every current action. -/
theorem coefficientNumber_lie (x : Cur) (ν : NB) :
    LieChains.derivExt (1 : Module.End ℂ Cur) ⁅x, ν⁆ =
      ⁅x, LieChains.derivExt (1 : Module.End ℂ Cur) ν⁆ := by
  change LieChains.derivExt 1 (LieChains.derivExt (adCur x) ν) =
    LieChains.derivExt (adCur x) (LieChains.derivExt 1 ν)
  have hX : (1 : Module.End ℂ Cur) * adCur x - adCur x * 1 = 0 := by
    apply LinearMap.ext
    intro c
    simp
  rw [← sub_eq_zero, LieChains.derivExt_commutator, hX, LieChains.derivExt_zero_apply]

private theorem matrix_h_eq_tau : MatrixSL2.h = TauCeti.slFinTwoBasis ℂ 2 := by
  apply Subtype.ext
  rw [TauCeti.slFinTwoBasis_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [MatrixSL2.h]

private theorem matrix_e_eq_tau : MatrixSL2.e = TauCeti.slFinTwoBasis ℂ 0 := by
  apply Subtype.ext
  rw [TauCeti.slFinTwoBasis_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [MatrixSL2.e]

/-- The standard harmonic coefficient tensored with the actual exterior coefficient. -/
def standardTensorMap (p : ℕ) :
    TauCeti.Sl2Std ℂ (2*p) →ₗ[ℂ] NB →ₗ[ℂ] HarmN NB :=
  (TensorProduct.mk ℂ PositiveCE.Harmonic NB).comp
    (PositiveCE.standardHarmonicEmbedding p).toLinearMap

@[simp] theorem standardTensorMap_apply (p : ℕ)
    (v : TauCeti.Sl2Std ℂ (2*p)) (ν : NB) :
    standardTensorMap p v ν = PositiveCE.standardHarmonicEmbedding p v ⊗ₜ ν := rfl

/-- Diagonal constant actions give exactly the actual coinvariant relations. -/
theorem standardTensorMap_lie_mem (p : ℕ) (x : G)
    (v : TauCeti.Sl2Std ℂ (2*p)) (ν : NB) :
    standardTensorMap p ⁅x, v⁆ ν + standardTensorMap p v ⁅constant x, ν⁆ ∈ relH NB := by
  have h : actH NB x (PositiveCE.standardHarmonicEmbedding p v ⊗ₜ ν) ∈ relH NB :=
    Submodule.mem_iSup_of_mem x ⟨_, rfl⟩
  rw [actH, diag_tmul] at h
  change ⁅x, PositiveCE.standardHarmonicEmbedding p v⁆ ⊗ₜ ν +
    PositiveCE.standardHarmonicEmbedding p v ⊗ₜ ⁅constant x, ν⁆ ∈ relH NB at h
  rw [← (PositiveCE.standardHarmonicEmbedding p).map_lie x v] at h
  exact h

/-- Every tensor with a standard harmonic vector above coefficient degree is a relation. -/
theorem standardTensorMap_mem_relH_of_lt (B p : ℕ) (hp : B < p)
    (v : TauCeti.Sl2Std ℂ (2*p)) (ν : NB)
    (hν : LieChains.derivExt (1 : Module.End ℂ Cur) ν = (B : ℂ) • ν) :
    standardTensorMap p v ν ∈ relH NB := by
  let P := Module.End.eigenspace (LieChains.derivExt (1 : Module.End ℂ Cur)) (B : ℂ)
  let H := LieModule.toEnd ℂ Cur NB (constant MatrixSL2.h)
  let E := LieModule.toEnd ℂ Cur NB (constant MatrixSL2.e)
  apply standard_bilinear_mem_of_shift_surjective (2*p) P (relH NB) H E
    (standardTensorMap p) ?_ ?_ ?_ ?_ v ν
    (Module.End.mem_eigenspace_iff.mpr hν)
  · intro w x _
    have hh := standardTensorMap_lie_mem p MatrixSL2.h w x
    have he : ⁅MatrixSL2.h, w⁆ = TauCeti.Sl2Std.diag ℂ (2*p) w := by
      rw [matrix_h_eq_tau, TauCeti.Sl2Std.lie_slFinTwoBasis_two]
    rw [he] at hh
    exact hh
  · intro w x _
    have hh := standardTensorMap_lie_mem p MatrixSL2.e w x
    have he : ⁅MatrixSL2.e, w⁆ = TauCeti.Sl2Std.raise ℂ (2*p) w := by
      rw [matrix_e_eq_tau, TauCeti.Sl2Std.lie_slFinTwoBasis_zero]
    rw [he] at hh
    exact hh
  · intro x hx
    have hx' := Module.End.mem_eigenspace_iff.mp hx
    apply Module.End.mem_eigenspace_iff.mpr
    change LieChains.derivExt (1 : Module.End ℂ Cur) ⁅constant MatrixSL2.e, x⁆ =
      (B : ℂ) • ⁅constant MatrixSL2.e, x⁆
    rw [coefficientNumber_lie, hx', lie_smul]
  · intro x hx
    obtain ⟨y, hy, he⟩ := coefficient_cartan_sub_surjective B p hp x
      (Module.End.mem_eigenspace_iff.mp hx)
    refine ⟨y, Module.End.mem_eigenspace_iff.mpr hy, ?_⟩
    change ⁅constant MatrixSL2.h, y⁆ - ((2*p : ℕ) : ℂ) • y = x
    rw [Nat.cast_mul, Nat.cast_ofNat]
    exact he

/-- The harmonic-degree-p coefficient tensors vanish modulo constants whenever B<p. -/
theorem tmul_mem_relH_of_lt (B p : ℕ) (hp : B < p)
    (h : PositiveCE.Harmonic) (hh : h ∈ degH p) (ν : NB)
    (hν : LieChains.derivExt (1 : Module.End ℂ Cur) ν = (B : ℂ) • ν) :
    h ⊗ₜ[ℂ] ν ∈ relH NB := by
  let e := PositiveCE.harmonicDegreeStandardEquiv p
  have he : PositiveCE.standardHarmonicEmbedding p (e ⟨h, hh⟩) = h :=
    congrArg Subtype.val (e.symm_apply_apply ⟨h, hh⟩)
  have hm := standardTensorMap_mem_relH_of_lt B p hp (e ⟨h, hh⟩) ν hν
  rw [standardTensorMap_apply, he] at hm
  exact hm

/-- The actual harmonic window consists of constant-sl₂ relations above degree B. -/
theorem harmWin_le_relH_of_lt (B p : ℕ) (hp : B < p) (S : ℤ) :
    harmWin p B S ≤ relH NB :=
  harmWin_le_of_tmul p B S (relH NB) (tmul_mem_relH_of_lt B p hp)

/-- Unconditional vanishing of the actual BGG term above coefficient degree. -/
theorem bggTerm_eq_bot_of_lt (B p : ℕ) (hp : B < p) (S : ℤ) :
    bggTerm p B S = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨z, hz, rfl⟩
  rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact harmWin_le_relH_of_lt B p hp S hz

end KhanSL2.BGGBridge
