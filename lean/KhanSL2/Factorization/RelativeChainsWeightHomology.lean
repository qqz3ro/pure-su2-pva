module

public import KhanSL2.Factorization.RelativeChainsWeightRelations
public import KhanSL2.Factorization.RelativeChainsDualityPerfect

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The actual boundary and its transpose on finite relative CE blocks, followed
by perfect homology duality. All quotient maps retain their evaluation formulas. -/

noncomputable section
namespace KhanSL2.Factorization
open Macdonald BGGBridge

/-- Restrict the genuine CE boundary to its finite mixed-coordinate block. -/
def rawWeightBoundary (w s : ℕ) : Module.End ℂ (weightDegreePiece w s) :=
  chainBoundary.restrict (fun u hu => chainBoundary_preservesWeightDegree w s u hu)

@[simp] theorem rawWeightBoundary_val (w s : ℕ) (u : weightDegreePiece w s) :
    (rawWeightBoundary w s u).val = chainBoundary u.val := rfl

theorem chainModel_symm_chainBoundary (u : W) :
    chainModel.symm (chainBoundary u) = rawDifferential SymmetricCoefficients (chainModel.symm u) := by
  simp [chainBoundary]

theorem rawWeightBoundary_mem_relations (w s : ℕ) {u : weightDegreePiece w s}
    (hu : u ∈ weightRelations w s) : rawWeightBoundary w s u ∈ weightRelations w s := by
  rw [mem_weightRelations, rawWeightBoundary_val, chainModel_symm_chainBoundary]
  exact relC_le_dC SymmetricCoefficients hu

/-- The actual induced boundary on the finite constant-coinvariant quotient. -/
def weightBoundary (w s : ℕ) : Module.End ℂ (WeightChains w s) :=
  (weightRelations w s).mapQ (weightRelations w s) (rawWeightBoundary w s)
    (fun _ hu => rawWeightBoundary_mem_relations w s hu)

@[simp] theorem weightBoundary_mk (w s : ℕ) (u : weightDegreePiece w s) :
    weightBoundary w s (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (rawWeightBoundary w s u) := rfl

theorem rawWeightBoundary_square_zero (w s : ℕ) (u : weightDegreePiece w s) :
    rawWeightBoundary w s (rawWeightBoundary w s u) = 0 := by
  apply Subtype.ext
  exact chainBoundary_square_zero u.val

theorem weightBoundary_square_zero (w s : ℕ) (u : WeightChains w s) :
    weightBoundary w s (weightBoundary w s u) = 0 := by
  induction u using Submodule.Quotient.induction_on with
  | H u => rw [weightBoundary_mk, weightBoundary_mk, rawWeightBoundary_square_zero,
      Submodule.Quotient.mk_zero]

theorem weightBoundary_comp_self (w s : ℕ) :
    (weightBoundary w s).comp (weightBoundary w s) = 0 :=
  LinearMap.ext (weightBoundary_square_zero w s)

theorem weightInclusion_boundary (w s : ℕ) (u : WeightChains w s) :
    weightInclusion w s (weightBoundary w s u) =
      differential SymmetricCoefficients (weightInclusion w s u) := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    rw [weightBoundary_mk, weightInclusion_mk, weightInclusion_mk, differential_mk,
      rawWeightBoundary_val, chainModel_symm_chainBoundary]

theorem weightComponent_differential (w s : ℕ) (u : RelativeChains SymmetricCoefficients) :
    weightComponent w s (differential SymmetricCoefficients u) =
      weightBoundary w s (weightComponent w s u) := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    rw [differential_mk, weightComponent_mk, weightComponent_mk, weightBoundary_mk]
    congr 1
    apply Subtype.ext
    simp only [rawWeightComponent_val, rawWeightBoundary_val,
      ← chainBoundary_chainModel, weightProjection_chainBoundary]

/-- The actual restricted transpose, further restricted to constant invariants. -/
def weightCoboundary (w s : ℕ) : Module.End ℂ (weightCochains w s) where
  toFun u := ⟨⟨Macdonald.differential u.val.val,
    restrictedTranspose_mem_weightDegree chainBoundary u.val.property⟩,
      differential_mem_relativeCochains u.property⟩
  map_add' u v := by apply Subtype.ext; apply Subtype.ext; exact map_add _ _ _
  map_smul' r u := by apply Subtype.ext; apply Subtype.ext; exact map_smul _ _ _

@[simp] theorem weightCoboundary_val (w s : ℕ) (u : weightCochains w s) :
    (weightCoboundary w s u).val.val = Macdonald.differential u.val.val := rfl

theorem weightCoboundary_square_zero (w s : ℕ) (u : weightCochains w s) :
    weightCoboundary w s (weightCoboundary w s u) = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  exact Macdonald.differential_square_zero u.val.val

theorem weightCoboundary_comp_self (w s : ℕ) :
    (weightCoboundary w s).comp (weightCoboundary w s) = 0 :=
  LinearMap.ext (weightCoboundary_square_zero w s)

/-- The perfect finite quotient Macdonald.pairing intertwines the actual two differentials. -/
theorem weightRelativeDualEquiv_transpose (w s : ℕ) :
    (weightRelativeDualEquiv w s).toLinearMap.comp (weightCoboundary w s) =
      (weightBoundary w s).dualMap.comp (weightRelativeDualEquiv w s).toLinearMap := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    change weightRelativeDualEquiv w s (weightCoboundary w s u) (Submodule.Quotient.mk v) =
      weightRelativeDualEquiv w s u (weightBoundary w s (Submodule.Quotient.mk v))
    rw [weightBoundary_mk, weightRelativeDualEquiv_mk, weightRelativeDualEquiv_mk,
      weightCoboundary_val, rawWeightBoundary_val, differential_pairing]

/-- A specified isomorphism to the dual short complex, using the original pairing. -/
def weightDualPair (w s : ℕ) :
    PerfectDuality.PairEquiv (weightCoboundary w s) (weightCoboundary w s)
      (weightBoundary w s).dualMap (weightBoundary w s).dualMap where
  left := weightRelativeDualEquiv w s
  middle := weightRelativeDualEquiv w s
  right := weightRelativeDualEquiv w s
  comm_in := weightRelativeDualEquiv_transpose w s
  comm_out := weightRelativeDualEquiv_transpose w s

abbrev WeightHomology (w s : ℕ) :=
  PerfectDuality.PairHomology (weightBoundary w s) (weightBoundary w s)
    (weightBoundary_comp_self w s)

abbrev WeightCohomology (w s : ℕ) :=
  PerfectDuality.PairHomology (weightCoboundary w s) (weightCoboundary w s)
    (weightCoboundary_comp_self w s)

/-- Canonical perfect duality between finite actual relative CE homology and
restricted relative CE cohomology of the same loop-weight and symmetric degree. -/
def weightHomologyDualEquiv (w s : ℕ) :
    WeightCohomology w s ≃ₗ[ℂ] Module.Dual ℂ (WeightHomology w s) :=
  PerfectDuality.pairedHomologyEquiv (weightBoundary w s) (weightBoundary w s)
    (weightDualPair w s) (weightCoboundary_comp_self w s) (weightBoundary_comp_self w s)

/-- The homology duality evaluates the original factorial Macdonald.pairing on cycle representatives. -/
@[simp] theorem weightHomologyDualEquiv_mk (w s : ℕ)
    (u : LinearMap.ker (weightCoboundary w s)) (v : LinearMap.ker (weightBoundary w s)) :
    weightHomologyDualEquiv w s (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) =
      weightRelativeDualEquiv w s u.val v.val := rfl

end KhanSL2.Factorization
