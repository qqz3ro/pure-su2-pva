module

public import KhanSL2.Macdonald.StrongBridgeHomologyPairing
public import KhanSL2.Macdonald.MixedCoproductComparison
public import KhanSL2.Factorization.ShuffleSymmetricKunneth

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The original harmonic cocycles evaluate actual relative tensor homology.
The only quotient descent is by the proved boundary-annihilation identities. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald
open Factorization BGGBridge

/-- A functional annihilating d descends to the actual cycle/image quotient. -/
def totalCocycleEvaluation {A : Type*} [AddCommGroup A] [Module ℂ A]
    (d : Module.End ℂ A) (f : Module.Dual ℂ A) (hf : ∀ a, f (d a) = 0) :
    Module.Dual ℂ (LinearMap.ker d ⧸ PerfectDuality.pairBoundaries d d) :=
  (PerfectDuality.pairBoundaries d d).liftQ (f.comp (LinearMap.ker d).subtype) (by
    rintro u ⟨v,hv⟩
    change d v = u.val at hv
    change f u.val = 0
    rw [← hv]
    exact hf v)

@[simp] theorem totalCocycleEvaluation_mk {A : Type*} [AddCommGroup A] [Module ℂ A]
    (d : Module.End ℂ A) (f : Module.Dual ℂ A) (hf : ∀ a, f (d a) = 0)
    (u : LinearMap.ker d) : totalCocycleEvaluation d f hf (Submodule.Quotient.mk u) = f u.val := rfl

/-- The specified Gmap expression is an actual invariant cocycle. -/
def strongFreeRelativeCycle (u : strongFree) : relativeCycles :=
  strongHarmonicCycle (strongFreeToHarmonic u)

@[simp] theorem strongFreeRelativeCycle_val (u : strongFree) :
    (strongFreeRelativeCycle u).val.val = strongModel (StrongMacdonald.Gmap u.val) := rfl

def strongFreeRelativeEvaluation (u : strongFree) :
    Module.Dual ℂ (RelativeChains SymmetricCoefficients) :=
  relativeEvaluation (strongFreeRelativeCycle u).val

@[simp] theorem strongFreeRelativeEvaluation_mk (u : strongFree)
    (z : RawChains SymmetricCoefficients) :
    strongFreeRelativeEvaluation u (Submodule.Quotient.mk z) =
      pairing (strongModel (StrongMacdonald.Gmap u.val)) (chainModel z) := rfl

theorem strongFreeRelativeEvaluation_differential (u : strongFree)
    (z : RelativeChains SymmetricCoefficients) :
    strongFreeRelativeEvaluation u (Factorization.differential SymmetricCoefficients z) = 0 := by
  change relativeEvaluation (strongFreeRelativeCycle u).val
    (Factorization.differential SymmetricCoefficients z) = 0
  rw [← relativeEvaluation_differential]
  have hz : relativeDifferential (strongFreeRelativeCycle u).val = 0 :=
    (strongFreeRelativeCycle u).property
  rw [hz]
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (relC SymmetricCoefficients) z
  simp only [Submodule.mkQ_apply,relativeEvaluation_mk]
  simp

/-- The normalized homology model evaluates the actual invariant cocycle on any cycle. -/
theorem strongFreeRelativeEvaluation_cycle (u : strongFree)
    (z : LinearMap.ker (Factorization.differential SymmetricCoefficients)) :
    strongFreeRelativeEvaluation u z.val =
      pairing (strongModel u.val)
        (strongModel (strongTotalHomologyFreeEquiv (Submodule.Quotient.mk z)).val) := by
  obtain ⟨v,hv⟩ := Submodule.mkQ_surjective (relC SymmetricCoefficients) z.val
  have hd : Factorization.differential SymmetricCoefficients (Submodule.Quotient.mk v) = 0 := by
    change Factorization.differential SymmetricCoefficients ((relC SymmetricCoefficients).mkQ v) = 0
    rw [hv]
    exact z.property
  have he : totalSymmetricCycleClass v hd = Submodule.Quotient.mk z := by
    have hh : (⟨Submodule.Quotient.mk v,hd⟩ :
        LinearMap.ker (Factorization.differential SymmetricCoefficients)) = z :=
      Subtype.ext hv
    exact congrArg (squareZeroClass (Factorization.differential SymmetricCoefficients)) hh
  rw [← he,strongTotalHomologyFreeEquiv_pairing_cycle,← hv]
  exact strongFreeRelativeEvaluation_mk u v

/-- Product of the actual invariant cochain functionals on the relative tensor. -/
def strongFreeTensorEvaluation (u v : strongFree) :
    Module.Dual ℂ (RelativeChains SymmetricCoefficients ⊗[ℂ] RelativeChains SymmetricCoefficients) :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp
    (TensorProduct.map (strongFreeRelativeEvaluation u) (strongFreeRelativeEvaluation v))

@[simp] theorem strongFreeTensorEvaluation_tmul (u v : strongFree)
    (z t : RelativeChains SymmetricCoefficients) :
    strongFreeTensorEvaluation u v (z ⊗ₜ[ℂ] t) =
      strongFreeRelativeEvaluation u z * strongFreeRelativeEvaluation v t := by
  simp [strongFreeTensorEvaluation,smul_eq_mul]

theorem strongFreeTensorEvaluation_differential (u v : strongFree)
    (z : RelativeChains SymmetricCoefficients ⊗[ℂ] RelativeChains SymmetricCoefficients) :
    strongFreeTensorEvaluation u v
      (relativeTensorDifferential SymmetricCoefficients SymmetricCoefficients z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z t hz ht => simp only [map_add,hz,ht,add_zero]
  | tmul z t =>
    rw [relativeTensorDifferential_tmul,map_add,strongFreeTensorEvaluation_tmul,
      strongFreeTensorEvaluation_tmul,strongFreeRelativeEvaluation_differential,
      strongFreeRelativeEvaluation_differential]
    simp

/-- The finite tensor pairing descends through the actual signed total boundary. -/
def strongFreeTensorHomologyEvaluation (u v : strongFree) :
    Module.Dual ℂ (TensorTotalHomology SymmetricCoefficients SymmetricCoefficients) :=
  totalCocycleEvaluation (relativeTensorDifferential SymmetricCoefficients SymmetricCoefficients)
    (strongFreeTensorEvaluation u v) (strongFreeTensorEvaluation_differential u v)

/-- The normalized homology-to-coordinate map, with its original factorial convention. -/
def strongHomologyModel : TotalHomology SymmetricCoefficients →ₗ[ℂ] W :=
  strongModel.toLinearMap.comp (strongFree.subtype.comp strongTotalHomologyFreeEquiv.toLinearMap)

@[simp] theorem strongHomologyModel_apply (h : TotalHomology SymmetricCoefficients) :
    strongHomologyModel h = strongModel (strongTotalHomologyFreeEquiv h).val := rfl

/-- Canonical Künneth and the harmonic tensor pairing agree on all homology tensors. -/
theorem strongFreeTensorHomologyEvaluation_kunneth (u v : strongFree)
    (h : TotalHomology SymmetricCoefficients ⊗[ℂ] TotalHomology SymmetricCoefficients) :
    strongFreeTensorHomologyEvaluation u v
      (totalKunnethEquiv SymmetricCoefficients SymmetricCoefficients h) =
      tensorSquarePairing (strongModel u.val ⊗ₜ[ℂ] strongModel v.val)
        (TensorProduct.map strongHomologyModel strongHomologyModel h) := by
  induction h using TensorProduct.induction_on with
  | zero => simp
  | add h k hh hk => simp only [map_add,hh,hk]
  | tmul h k =>
    obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective
      (PerfectDuality.pairBoundaries (Factorization.differential SymmetricCoefficients)
        (Factorization.differential SymmetricCoefficients)) h
    obtain ⟨t,rfl⟩ := Submodule.mkQ_surjective
      (PerfectDuality.pairBoundaries (Factorization.differential SymmetricCoefficients)
        (Factorization.differential SymmetricCoefficients)) k
    simp only [Submodule.mkQ_apply]
    rw [totalKunnethEquiv_mk_tmul_mk,TensorProduct.map_tmul,tensorSquarePairing_tmul]
    change strongFreeTensorEvaluation u v (z.val ⊗ₜ[ℂ] t.val) = _
    rw [strongFreeTensorEvaluation_tmul,strongFreeRelativeEvaluation_cycle,
      strongFreeRelativeEvaluation_cycle]
    rfl

/-- Every actual tensor-homology class is evaluated through the same canonical inverse. -/
theorem strongFreeTensorHomologyEvaluation_inverse (u v : strongFree)
    (h : TensorTotalHomology SymmetricCoefficients SymmetricCoefficients) :
    strongFreeTensorHomologyEvaluation u v h =
      tensorSquarePairing (strongModel u.val ⊗ₜ[ℂ] strongModel v.val)
        (TensorProduct.map strongHomologyModel strongHomologyModel
          ((totalKunnethEquiv SymmetricCoefficients SymmetricCoefficients).symm h)) := by
  simpa only [LinearEquiv.apply_symm_apply] using
    strongFreeTensorHomologyEvaluation_kunneth u v
      ((totalKunnethEquiv SymmetricCoefficients SymmetricCoefficients).symm h)

end KhanSL2.Macdonald
