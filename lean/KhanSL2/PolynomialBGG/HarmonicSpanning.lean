module

public import KhanSL2.BGGBridge.CoefficientProjection
public import KhanSL2.BGGBridge.TermVanishing

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct
namespace KhanSL2.BGGBridge
open KhanSL2.BGG KhanSL2.Current

/-- A subspace containing tensors with each harmonic standard basis vector contains
all standard tensors. The coefficient vector is held fixed. -/
theorem standardTensorMap_mem_of_basis (p : ℕ) (W : Submodule ℂ (HarmN NB))
    (ν : NB)
    (h : ∀ i : Fin (2*p+1),
      standardTensorMap p (TauCeti.Sl2Std.basis ℂ (2*p) i) ν ∈ W)
    (v : TauCeti.Sl2Std ℂ (2*p)) : standardTensorMap p v ν ∈ W := by
  have hs : (⊤ : Submodule ℂ (TauCeti.Sl2Std ℂ (2*p))) ≤
      W.comap ((standardTensorMap p).flip ν) := by
    rw [← (TauCeti.Sl2Std.basis ℂ (2*p)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  exact hs (Submodule.mem_top : v ∈ (⊤ : Submodule ℂ (TauCeti.Sl2Std ℂ (2*p))))

/-- Standard harmonic basis vectors test membership of every actual harmonic
window, with no extremal-weight or polynomial-module hypothesis. -/
theorem harmWin_le_of_standardBasis (p B : ℕ) (S : ℤ)
    (W : Submodule ℂ (HarmN NB))
    (ht : ∀ i : Fin (2*p+1), ∀ ν : NB,
      LieChains.derivExt (1 : Module.End ℂ Cur) ν = (B : ℂ) • ν →
      standardTensorMap p (TauCeti.Sl2Std.basis ℂ (2*p) i) ν ∈ W) :
    harmWin p B S ≤ W := by
  apply harmWin_le_of_tmul p B S W
  intro h hh ν hν
  let e := PositiveCE.harmonicDegreeStandardEquiv p
  have he : PositiveCE.standardHarmonicEmbedding p (e ⟨h, hh⟩) = h :=
    congrArg Subtype.val (e.symm_apply_apply ⟨h, hh⟩)
  have hm := standardTensorMap_mem_of_basis p W ν (fun i => ht i ν hν) (e ⟨h, hh⟩)
  rw [standardTensorMap_apply, he] at hm
  exact hm

end KhanSL2.BGGBridge
