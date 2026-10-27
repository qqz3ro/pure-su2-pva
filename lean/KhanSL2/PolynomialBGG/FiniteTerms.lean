module

public import KhanSL2.PolynomialBGG.RootRing
public import KhanSL2.PolynomialBGG.ColoredClasses
public import KhanSL2.PolynomialBGG.HarmonicSpanning
public import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace KhanSL2.PolynomialBGG

open MvPolynomial BGG Current BGGBridge Conditional
open scoped TensorProduct KhanSL2.Conditional

/-- The finite collection of harmonic basis vectors and slot-color choices. -/
abbrev ColorIndex (B p : ℕ) := Fin (2*p+1) × (Fin B → Fin 3)

/-- Each colored coefficient map is linear over the prescribed elementary coordinates. -/
def coloredClassLinear (B p : ℕ) (j : ColorIndex B p) :
    RootPolynomial B →ₗ[CoefficientRing B] (HarmN NB ⧸ relH NB) where
  toFun q := coloredClassMap B p (TauCeti.Sl2Std.basis ℂ (2*p) j.1) j.2 q
  map_add' q r := map_add _ q r
  map_smul' r q := by
    change coloredClassMap B p (TauCeti.Sl2Std.basis ℂ (2*p) j.1) j.2
      (r • q : RootPolynomial B) = _
    rw [rootPolynomial_smul]
    exact coloredClassMap_symmetric B p _ _ r q

/-- Sum the finitely many colored polynomial maps into genuine coinvariants. -/
def coloredTotalMap (B p : ℕ) :
    (ColorIndex B p → RootPolynomial B) →ₗ[CoefficientRing B] (HarmN NB ⧸ relH NB) :=
  ∑ j : ColorIndex B p, (coloredClassLinear B p j).comp (LinearMap.proj j)

@[simp] theorem coloredTotalMap_single (B p : ℕ) (j : ColorIndex B p)
    (q : RootPolynomial B) :
    coloredTotalMap B p (Pi.single j q) = coloredClassLinear B p j q := by
  classical
  simp only [coloredTotalMap, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [hkj]
  · simp

/-- A finite coefficient module inside the full coinvariant quotient. -/
def coloredImage (B p : ℕ) : Submodule (CoefficientRing B) (HarmN NB ⧸ relH NB) :=
  (coloredTotalMap B p).range

instance coloredImage_finite (B p : ℕ) : Module.Finite (CoefficientRing B) (coloredImage B p) := by
  exact Module.Finite.range (coloredTotalMap B p)

theorem coloredClassMap_mem_image (B p : ℕ) (j : ColorIndex B p)
    (q : MvPolynomial (Fin B) ℂ) :
    coloredClassMap B p (TauCeti.Sl2Std.basis ℂ (2*p) j.1) j.2 q ∈ coloredImage B p := by
  refine ⟨Pi.single j (show RootPolynomial B from q), ?_⟩
  exact coloredTotalMap_single B p j q

/-- Every actual homogeneous BGG term lies in the finite colored polynomial image. -/
theorem bggTerm_le_coloredImage (B p : ℕ) (S : ℤ) :
    bggTerm p B S ≤ (coloredImage B p).restrictScalars ℂ := by
  let W : Submodule ℂ (HarmN NB) :=
    ((coloredImage B p).restrictScalars ℂ).comap (relH NB).mkQ
  have hW : harmWin p B S ≤ W := by
    apply harmWin_le_of_standardBasis p B S W
    intro i ν hν
    change coefficientClass p (TauCeti.Sl2Std.basis ℂ (2*p) i) ν ∈ coloredImage B p
    apply coefficient_degree_le_of_coloredWord B
      (((coloredImage B p).restrictScalars ℂ).comap
        (coefficientClass p (TauCeti.Sl2Std.basis ℂ (2*p) i))) _ ν hν
    intro c a
    change coefficientClass p (TauCeti.Sl2Std.basis ℂ (2*p) i) (coloredWord B c a) ∈
      coloredImage B p
    rw [← coloredClassMap_product]
    exact coloredClassMap_mem_image B p (i, c) _
  rintro q ⟨z, hz, rfl⟩
  exact hW hz

theorem termToCoinvariants_mem_coloredImage (B p : ℕ) (x : BGGComplex.Term B p) :
    BGGComplex.termToCoinvariants B p x ∈ coloredImage B p := by
  have hrange : LinearMap.range (BGGComplex.termToCoinvariants B p) ≤
      (coloredImage B p).restrictScalars ℂ := by
    change LinearMap.range (DirectSum.coeLinearMap (bggTerm p B)) ≤ _
    rw [DirectSum.range_coeLinearMap]
    exact iSup_le (bggTerm_le_coloredImage B p)
  exact hrange ⟨x, rfl⟩

/-- The actual BGG term embeds into the finite colored coefficient module. -/
def termToColoredImage (B p : ℕ) :
    BGGComplex.Term B p →ₗ[CoefficientRing B] coloredImage B p :=
  (BGGComplex.termToCoinvariantsLinear B p).codRestrict (coloredImage B p)
    (termToCoinvariants_mem_coloredImage B p)

theorem termToColoredImage_injective (B p : ℕ) :
    Function.Injective (termToColoredImage B p) := by
  intro x y hxy
  apply BGGComplex.termToCoinvariants_injective B p
  exact congrArg Subtype.val hxy

/-- Finite generation of each actual BGG term for its canonical coefficient action. -/
theorem bggTerm_finite (B p : ℕ) : Module.Finite (CoefficientRing B) (BGGComplex.Term B p) :=
  Module.Finite.of_injective (termToColoredImage B p) (termToColoredImage_injective B p)

end KhanSL2.PolynomialBGG
