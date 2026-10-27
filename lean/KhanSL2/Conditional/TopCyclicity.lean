module

public import KhanSL2.Conditional.TopEmbedding
public import KhanSL2.BGGBridge.TopPolynomialMap
public import KhanSL2.BGGBridge.TopAlternants
public import KhanSL2.BGGBridge.TopWeightBasis

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
namespace KhanSL2.Conditional
open BGGBridge Current
open scoped KhanSL2.Conditional

namespace BGGComplex

/-- The consecutive-mode wedge, paired with the bottom harmonic vector. -/
def topGenerator (B : ℕ) : Term B B :=
  DirectSum.lof ℂ ℤ (fun S => ↥(bggTerm B B S)) (topGeneratorSpin B) (topGeneratorWindow B)

theorem topGenerator_image (B : ℕ) :
    termToCoinvariants B B (topGenerator B) =
      topPolynomialMap B
        (∏ i : Fin B, (MvPolynomial.X i : MvPolynomial (Fin B) ℂ) ^ i.val) := by
  rw [topGenerator, termToCoinvariants_lof, topGeneratorWindow_coe]

/-- Every extremal coefficient class is a polynomial multiple of the consecutive word. -/
theorem topPolynomialMap_exists_smul (B : ℕ) (p : MvPolynomial (Fin B) ℂ) :
    ∃ r : CoefficientRing B, topPolynomialMap B p =
      r • termToCoinvariants B B (topGenerator B) := by
  rw [topGenerator_image]
  exact TopAlternants.exists_smul_of_powerSums (coefficientCoordinates B)
    (topPolynomialMap B) (topPolynomialMap_rename B)
    (fun i q => (topPolynomialMap_powerSum (i.val + 1) B q).trans
      (globalCoefficientCoordinates_smul B i (topPolynomialMap B q)).symm) p

/-- The actual top BGG term is cyclic for its already constructed coefficient action. -/
theorem topGenerator_surjective (B : ℕ) :
    Function.Surjective (LinearMap.toSpanSingleton (CoefficientRing B) (Term B B)
      (topGenerator B)) := by
  let W : Submodule (CoefficientRing B) (HarmN NB ⧸ relH NB) :=
    Submodule.span (CoefficientRing B) {termToCoinvariants B B (topGenerator B)}
  let WC : Submodule ℂ (HarmN NB ⧸ relH NB) := W.restrictScalars ℂ
  let P : Submodule ℂ (HarmN NB) := WC.comap (relH NB).mkQ
  have hrel : relH NB ≤ P := by
    intro z hz
    change (relH NB).mkQ z ∈ WC
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hz]
    exact WC.zero_mem
  have htop : ∀ q, q ∈ coefficientTopSubspace B →
      standardTensorMap B (TauCeti.Sl2Std.basisVector ℂ (2*B) (2*B)) q ∈ P := by
    apply coefficientTopSubspace_le_of_ιMulti B
      (P.comap (standardTensorMap B (TauCeti.Sl2Std.basisVector ℂ (2*B) (2*B))))
    intro d
    change topCoefficientClass B
      (ExteriorAlgebra.ιMulti ℂ B (fun i => BGG.currentBasis (d i, 0))) ∈ W
    rw [← topPolynomialMap_product]
    obtain ⟨r, hr⟩ := topPolynomialMap_exists_smul B
      (∏ i : Fin B, (MvPolynomial.X i : MvPolynomial (Fin B) ℂ) ^ d i)
    rw [hr]
    exact W.smul_mem r (Submodule.subset_span (Set.mem_singleton _))
  have hwin (S : ℤ) : bggTerm B B S ≤ WC := by
    rintro q ⟨z, hz, rfl⟩
    exact harmWin_top_le B S P hrel htop hz
  have hrange : LinearMap.range (termToCoinvariants B B) ≤ WC := by
    change LinearMap.range (DirectSum.coeLinearMap (bggTerm B B)) ≤ WC
    rw [DirectSum.range_coeLinearMap]
    exact iSup_le hwin
  intro x
  have hx : termToCoinvariants B B x ∈ W := hrange ⟨x, rfl⟩
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hx
  refine ⟨r, termToCoinvariants_injective B B ?_⟩
  change termToCoinvariants B B (r • topGenerator B) = termToCoinvariants B B x
  rw [termToCoinvariants_smul]
  exact hr

end BGGComplex
end KhanSL2.Conditional


