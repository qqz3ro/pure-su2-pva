module

public import KhanSL2.Macdonald.ChainGrading

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Restricted relative cochains are precisely the finite-coordinate
functionals annihilating the actual constant-sl2 chain relations. The
comparison into the full dual of relative chains is injective, but is not
asserted to be surjective in infinite dimension. -/
noncomputable section
namespace KhanSL2.Macdonald

/-- Evaluate mixed coordinates on the actual symmetric-coefficient CE chains. -/
def chainPairing : W →ₗ[ℂ] Module.Dual ℂ (Factorization.RawChains SymmetricCoefficients) :=
  pairing.compl₂ chainModel.toLinearMap

@[simp] theorem chainPairing_apply (u : W) (v : Factorization.RawChains SymmetricCoefficients) :
    chainPairing u v = pairing u (chainModel v) := rfl

/-- Constant invariants in the restricted dual, as an annihilator of relations. -/
def relativeCochains : Submodule ℂ W :=
  (BGGBridge.relC SymmetricCoefficients).dualAnnihilator.comap chainPairing

instance relativeCochainsAddCommGroup : AddCommGroup relativeCochains :=
  Submodule.addCommGroup relativeCochains

theorem mem_relativeCochains (u : W) :
    u ∈ relativeCochains ↔ ∀ v ∈ BGGBridge.relC SymmetricCoefficients,
      pairing u (chainModel v) = 0 := by
  simp only [relativeCochains, Submodule.mem_comap, Submodule.mem_dualAnnihilator,
    chainPairing_apply]

/-- Evaluation factors through the actual relative-chain quotient. -/
def relativeEvaluation (u : relativeCochains) :
    Module.Dual ℂ (Factorization.RelativeChains SymmetricCoefficients) :=
  (BGGBridge.relC SymmetricCoefficients).liftQ (chainPairing u.val)
    (fun v hv => (mem_relativeCochains u.val).mp u.property v hv)

@[simp] theorem relativeEvaluation_mk (u : relativeCochains)
    (v : Factorization.RawChains SymmetricCoefficients) :
    relativeEvaluation u (Submodule.Quotient.mk v) = pairing u.val (chainModel v) := rfl

theorem relativeEvaluation_injective : Function.Injective relativeEvaluation := by
  intro u v h
  apply Subtype.ext
  have hz : u.val - v.val = 0 := by
    apply pairing_nondegenerate
    intro w
    obtain ⟨z,rfl⟩ := chainModel.surjective w
    have hh := LinearMap.congr_fun h (Submodule.Quotient.mk z)
    change pairing u.val (chainModel z) = pairing v.val (chainModel z) at hh
    simp only [map_sub, LinearMap.sub_apply, hh, sub_self]
  exact sub_eq_zero.mp hz

/-- The coboundary preserves constant invariance because the boundary
preserves the actual constant-chain relations. -/
theorem differential_mem_relativeCochains {u : W} (hu : u ∈ relativeCochains) :
    differential u ∈ relativeCochains := by
  apply (mem_relativeCochains _).mpr
  intro v hv
  rw [differential_pairing, chainBoundary_chainModel]
  exact (mem_relativeCochains u).mp hu _ (BGGBridge.relC_le_dC SymmetricCoefficients hv)

def relativeDifferential : Module.End ℂ relativeCochains :=
  differential.restrict (fun _ hu => differential_mem_relativeCochains hu)

@[simp] theorem relativeDifferential_val (u : relativeCochains) :
    (relativeDifferential u).val = differential u.val := rfl

theorem relativeDifferential_square_zero (u : relativeCochains) :
    relativeDifferential (relativeDifferential u) = 0 := by
  apply Subtype.ext
  exact differential_square_zero u.val

/-- Actual compatibility with the differential of relative CE chains. -/
theorem relativeEvaluation_differential (u : relativeCochains)
    (v : Factorization.RelativeChains SymmetricCoefficients) :
    relativeEvaluation (relativeDifferential u) v =
      relativeEvaluation u (Factorization.differential SymmetricCoefficients v) := by
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    change pairing (differential u.val) (chainModel v) =
      pairing u.val (chainModel (Factorization.rawDifferential SymmetricCoefficients v))
    rw [differential_pairing, chainBoundary_chainModel]

/-- Cycles in the actual restricted relative complex. -/
def relativeCycles : Submodule ℂ relativeCochains := LinearMap.ker relativeDifferential

instance relativeCyclesAddCommGroup : AddCommGroup relativeCycles :=
  Submodule.addCommGroup relativeCycles

/-- Boundaries, regarded as a submodule of cycles. -/
def relativeBoundaries : Submodule ℂ relativeCycles :=
  (LinearMap.range relativeDifferential).comap relativeCycles.subtype

/-- Total restricted relative CE cohomology with symmetric dual coefficients. -/
abbrev Cohomology : Type := relativeCycles ⧸ relativeBoundaries

end KhanSL2.Macdonald
