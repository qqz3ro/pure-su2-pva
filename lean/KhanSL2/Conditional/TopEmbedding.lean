module

public import KhanSL2.Conditional.BGGAction
public import KhanSL2.BGG.HarmonicEnergy

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open scoped TensorProduct

namespace KhanSL2.BGGBridge
open KhanSL2.BGG KhanSL2.Current

/-- Energy dilation commutes with the constant action on harmonic chains. -/
theorem harmonicEnergyScale_lie (x : G) (h : PositiveCE.Harmonic) :
    PositiveCE.harmonicEnergyScale ⁅x, h⁆ = ⁅x, PositiveCE.harmonicEnergyScale h⁆ := by
  apply Subtype.ext
  exact PositiveCE.energyScale_commute_of_piece (LieModule.toEnd ℂ G PositiveCE.Cochain x)
    id (fun _ _ _ hu => PositiveCE.positiveAction_mem_piece x hu) h

theorem dilH_actH (x : G) (z : HarmN NB) :
    dilH (actH NB x z) = actH NB x (dilH z) := by
  have hc : currentScale 2 (constant x) = constant x := by
    change currentScale 2 (mode 0 x) = mode 0 x
    rw [currentScale_mode, pow_zero, one_smul]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul h n =>
    simp only [actH, diag_tmul, dilH, TensorProduct.map_tmul, map_add,
      LieModule.toEnd_apply_apply, harmonicEnergyScale_lie, dilN_lie, hc]

/-- The physical-energy dilation on the genuine constant coinvariant quotient. -/
def dilHq : Module.End ℂ (HarmN NB ⧸ relH NB) :=
  (relH NB).mapQ (relH NB) dilH
    (le_comap_of_commute (actH NB) (actH NB) dilH dilH_actH)

theorem bggTerm_le_dilation_eigenspace (p B : ℕ) (S : ℤ) :
    bggTerm p B S ≤ Module.End.eigenspace dilHq ((2 : ℂ)^S) := by
  rintro q ⟨z, hz, rfl⟩
  apply Module.End.mem_eigenspace_iff.mpr
  change (relH NB).mkQ (dilH z) = (2 : ℂ)^S • (relH NB).mkQ z
  rw [Module.End.mem_eigenspace_iff.mp hz.2, map_smul]

theorem bggTerm_spin_independent (p B : ℕ) : iSupIndep (bggTerm p B) :=
  ((Module.End.eigenspaces_iSupIndep dilHq).comp energyEigenvalue_injective).mono
    (bggTerm_le_dilation_eigenspace p B)

end KhanSL2.BGGBridge

namespace KhanSL2.Conditional
open BGGBridge Current
open scoped KhanSL2.Conditional

/-- Polynomial coefficients act on the full harmonic coinvariant quotient. -/
def globalCoefficientAction (B : ℕ) :
    CoefficientRing B →ₐ[ℂ] Module.End ℂ (HarmN NB ⧸ relH NB) :=
  (Modules.commutingPolynomialEval
    (fun i : Fin B => coefficientBGGPower (i.val + 1))
    (fun i j => coefficientBGGPower_commute (i.val + 1) (j.val + 1))).comp
      (coefficientCoordinates B).symm.toAlgHom

instance globalCoefficientModule (B : ℕ) :
    Module (CoefficientRing B) (HarmN NB ⧸ relH NB) :=
  Module.compHom (HarmN NB ⧸ relH NB) (globalCoefficientAction B).toRingHom

instance globalCoefficientSMulCommClass (B : ℕ) :
    SMulCommClass ℂ (CoefficientRing B) (HarmN NB ⧸ relH NB) where
  smul_comm c a x := (map_smul (globalCoefficientAction B a) c x).symm

instance globalCoefficientIsScalarTower (B : ℕ) :
    IsScalarTower ℂ (CoefficientRing B) (HarmN NB ⧸ relH NB) where
  smul_assoc c a x :=
    LinearMap.congr_fun ((globalCoefficientAction B).toLinearMap.map_smul c a) x

theorem globalCoefficientCoordinates_smul (B : ℕ) (i : Fin B)
    (x : HarmN NB ⧸ relH NB) :
    coefficientCoordinates B (MvPolynomial.X i) • x = coefficientBGGPower (i.val + 1) x := by
  change (Modules.commutingPolynomialEval
    (fun j : Fin B => coefficientBGGPower (j.val + 1))
    (fun j k => coefficientBGGPower_commute (j.val + 1) (k.val + 1)))
    ((coefficientCoordinates B).symm (coefficientCoordinates B (MvPolynomial.X i))) x = _
  rw [AlgEquiv.symm_apply_apply]
  exact LinearMap.congr_fun (Modules.commutingPolynomialEval_X _ _ i) x

namespace BGGComplex

/-- Sum the actual homogeneous coinvariant terms in their common ambient quotient. -/
def termToCoinvariants (B p : ℕ) : Term B p →ₗ[ℂ] (HarmN NB ⧸ relH NB) :=
  DirectSum.coeLinearMap (bggTerm p B)

@[simp] theorem termToCoinvariants_lof (B p : ℕ) (S : ℤ) (x : bggTerm p B S) :
    termToCoinvariants B p (DirectSum.lof ℂ ℤ (fun T => ↥(bggTerm p B T)) S x) = x :=
  DirectSum.coeLinearMap_lof _ S x

theorem termToCoinvariants_injective (B p : ℕ) : Function.Injective (termToCoinvariants B p) :=
  (bggTerm_spin_independent p B).dfinsupp_lsum_injective

theorem termToCoinvariants_power (m B p : ℕ) (x : Term B p) :
    termToCoinvariants B p (coefficientPower m B p x) =
      coefficientBGGPower m (termToCoinvariants B p x) := by
  have h : (termToCoinvariants B p).comp (coefficientPower m B p) =
      (coefficientBGGPower m).comp (termToCoinvariants B p) := by
    apply DirectSum.linearMap_ext
    intro S
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, coefficientPower_lof, termToCoinvariants_lof]
    rfl
  exact LinearMap.congr_fun h x

theorem termToCoinvariants_smul (B p : ℕ) (a : CoefficientRing B) (x : Term B p) :
    termToCoinvariants B p (a • x) = a • termToCoinvariants B p x := by
  apply Modules.polynomialCoordinates_intertwines (coefficientCoordinates B)
    (termToCoinvariants B p) _ a x
  intro i z
  rw [coefficientCoordinates_smul, globalCoefficientCoordinates_smul]
  exact termToCoinvariants_power (i.val + 1) B p z

/-- The actual direct sum embeds over its fixed coefficient ring. -/
def termToCoinvariantsLinear (B p : ℕ) :
    Term B p →ₗ[CoefficientRing B] (HarmN NB ⧸ relH NB) where
  __ := (termToCoinvariants B p).toAddHom
  map_smul' := termToCoinvariants_smul B p

end BGGComplex
end KhanSL2.Conditional


