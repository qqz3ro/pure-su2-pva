module

public import KhanSL2.Factorization.RelativeChainsWeightProjection
public import KhanSL2.Factorization.RelativeChainsDualityQuotient

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Actual finite relative-chain blocks: the finite mixed block modulo precisely
those vectors which are genuine constant-sl2 relations. The quotient embeds in
actual relative CE chains, with its specified weight projection as a retraction. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.Factorization
open Macdonald BGGBridge

instance weightBlockAddCommGroup (w s : ℕ) : AddCommGroup (weightDegreePiece w s) :=
  Submodule.addCommGroup (weightDegreePiece w s)

/-- Weight projection in the existing exterior-first raw-chain coordinates. -/
def rawWeightProjection (w s : ℕ) : Module.End ℂ (RawChains SymmetricCoefficients) :=
  chainModel.symm.toLinearMap.comp ((weightProjection w s).comp chainModel.toLinearMap)

@[simp] theorem chainModel_rawWeightProjection (w s : ℕ)
    (z : RawChains SymmetricCoefficients) :
    chainModel (rawWeightProjection w s z) = weightProjection w s (chainModel z) := by
  simp [rawWeightProjection]

theorem rawWeightProjection_actC_color (w s : ℕ) (a : Fin 3)
    (z : RawChains SymmetricCoefficients) :
    rawWeightProjection w s (actC SymmetricCoefficients (MatrixSL2.color a) z) =
      actC SymmetricCoefficients (MatrixSL2.color a) (rawWeightProjection w s z) := by
  apply chainModel.injective
  simp only [chainModel_rawWeightProjection, chainModel_actC_color, weightProjection_colorAction]

theorem rawWeightProjection_actC (w s : ℕ) (x : BGG.G)
    (z : RawChains SymmetricCoefficients) :
    rawWeightProjection w s (actC SymmetricCoefficients x z) =
      actC SymmetricCoefficients x (rawWeightProjection w s z) := by
  rw [CEModel.actC_sum, CEModel.actC_sum]
  simp only [map_sum, map_smul, rawWeightProjection_actC_color]

theorem rawWeightProjection_mem_relations (w s : ℕ)
    {z : RawChains SymmetricCoefficients} (hz : z ∈ relC SymmetricCoefficients) :
    rawWeightProjection w s z ∈ relC SymmetricCoefficients :=
  le_comap_of_commute (actC SymmetricCoefficients) (actC SymmetricCoefficients)
    (rawWeightProjection w s) (rawWeightProjection_actC w s) hz

/-- The relations are the actual global relation subspace intersected with the finite block. -/
def weightRelations (w s : ℕ) : Submodule ℂ (weightDegreePiece w s) :=
  (relC SymmetricCoefficients).comap
    (chainModel.symm.toLinearMap.comp (weightDegreePiece w s).subtype)

@[simp] theorem mem_weightRelations (w s : ℕ) (u : weightDegreePiece w s) :
    u ∈ weightRelations w s ↔ chainModel.symm u.val ∈ relC SymmetricCoefficients := Iff.rfl

/-- The actual finite relative CE block, not an arbitrary isomorphic model. -/
abbrev WeightChains (w s : ℕ) := weightDegreePiece w s ⧸ weightRelations w s

/-- Inclusion of the finite block in the actual global relative quotient. -/
def weightInclusion (w s : ℕ) : WeightChains w s →ₗ[ℂ] RelativeChains SymmetricCoefficients :=
  (weightRelations w s).liftQ
    ((relC SymmetricCoefficients).mkQ.comp
      (chainModel.symm.toLinearMap.comp (weightDegreePiece w s).subtype))
    (by
      intro u hu
      change (relC SymmetricCoefficients).mkQ (chainModel.symm u.val) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr hu)

@[simp] theorem weightInclusion_mk (w s : ℕ) (u : weightDegreePiece w s) :
    weightInclusion w s (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (chainModel.symm u.val) := rfl

/-- Project a raw chain onto its specified finite coordinate block. -/
def rawWeightComponent (w s : ℕ) :
    RawChains SymmetricCoefficients →ₗ[ℂ] weightDegreePiece w s :=
  ((weightProjection w s).comp chainModel.toLinearMap).codRestrict _
    (fun z => weightProjection_mem w s (chainModel z))

@[simp] theorem rawWeightComponent_val (w s : ℕ) (z : RawChains SymmetricCoefficients) :
    (rawWeightComponent w s z).val = weightProjection w s (chainModel z) := rfl

theorem rawWeightComponent_mem_relations (w s : ℕ)
    {z : RawChains SymmetricCoefficients} (hz : z ∈ relC SymmetricCoefficients) :
    rawWeightComponent w s z ∈ weightRelations w s :=
  rawWeightProjection_mem_relations w s hz

/-- The finite block projection descends through the actual constant relations. -/
def weightComponent (w s : ℕ) : RelativeChains SymmetricCoefficients →ₗ[ℂ] WeightChains w s :=
  (relC SymmetricCoefficients).mapQ (weightRelations w s) (rawWeightComponent w s)
    (fun _ hz => rawWeightComponent_mem_relations w s hz)

@[simp] theorem weightComponent_mk (w s : ℕ) (z : RawChains SymmetricCoefficients) :
    weightComponent w s (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (rawWeightComponent w s z) := rfl

/-- Projection followed by inclusion recovers every finite-block quotient class. -/
@[simp] theorem weightComponent_inclusion (w s : ℕ) (z : WeightChains w s) :
    weightComponent w s (weightInclusion w s z) = z := by
  induction z using Submodule.Quotient.induction_on with
  | H u =>
    rw [weightInclusion_mk, weightComponent_mk]
    congr 1
    apply Subtype.ext
    rw [rawWeightComponent_val, chainModel.apply_symm_apply, weightProjection_of_mem u.property]

theorem weightInclusion_injective (w s : ℕ) : Function.Injective (weightInclusion w s) :=
  Function.LeftInverse.injective (weightComponent_inclusion w s)

/-- Restricted relative cochains in the same finite block. -/
def weightCochains (w s : ℕ) : Submodule ℂ (weightDegreePiece w s) :=
  relativeCochains.comap (weightDegreePiece w s).subtype

instance weightCochainsAddCommGroup (w s : ℕ) : AddCommGroup (weightCochains w s) :=
  Submodule.addCommGroup (weightCochains w s)

/-- Local annihilation and global relative invariance coincide because the genuine
relations are homogeneous and the Macdonald.pairing is block diagonal. -/
theorem weightCochains_eq_annihilator (w s : ℕ) :
    weightCochains w s = PerfectDuality.annihilator (weightDualEquiv w s) (weightRelations w s) := by
  ext u
  rw [PerfectDuality.mem_annihilator]
  change u.val ∈ relativeCochains ↔ _
  constructor
  · intro hu v hv
    have hh := (mem_relativeCochains u.val).mp hu (chainModel.symm v.val) hv
    simpa only [weightDualEquiv_apply, chainModel.apply_symm_apply] using hh
  · intro hu
    apply (mem_relativeCochains u.val).mpr
    intro z hz
    have hh := hu (rawWeightComponent w s z) (rawWeightComponent_mem_relations w s hz)
    change Macdonald.pairing u.val (weightProjection w s (chainModel z)) = 0 at hh
    rwa [pairing_weightProjection u.property] at hh

/-- Canonical perfect evaluation on the actual finite relative quotient. -/
def weightRelativeDualEquiv (w s : ℕ) :
    weightCochains w s ≃ₗ[ℂ] Module.Dual ℂ (WeightChains w s) :=
  (LinearEquiv.ofEq _ _ (weightCochains_eq_annihilator w s)).trans
    (PerfectDuality.annihilatorEquivDualQuotient (weightDualEquiv w s) (weightRelations w s))

@[simp] theorem weightRelativeDualEquiv_mk (w s : ℕ)
    (u : weightCochains w s) (v : weightDegreePiece w s) :
    weightRelativeDualEquiv w s u (Submodule.Quotient.mk v) = Macdonald.pairing u.val.val v.val := rfl

end KhanSL2.Factorization
