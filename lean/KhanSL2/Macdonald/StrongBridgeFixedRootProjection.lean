module

public import KhanSL2.Macdonald.StrongBridgeFixedRootInclusion
public import KhanSL2.Factorization.CoefficientTotalFunctor
public import KhanSL2.Factorization.ShuffleSymmetricKunnethProjection

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The actual symmetric-degree homology projection selects precisely the
corresponding root-model components. No projection is replaced by transport. -/
noncomputable section
open scoped TensorProduct DirectSum
namespace KhanSL2.Macdonald
open Factorization

@[simp] theorem coefficientTotalHomologyMap_symmetricInclusion (s : ℕ) :
    coefficientTotalHomologyMap (symmetricPower s).incl = symmetricHomologyInclusion s := by
  apply LinearMap.ext
  intro z
  obtain ⟨u,rfl⟩ := Submodule.mkQ_surjective
    (PerfectDuality.pairBoundaries (Factorization.differential (symmetricPower s))
      (Factorization.differential (symmetricPower s))) z
  rfl

/-- The original symmetric coefficient projection kills every other homogeneous power. -/
theorem symmetricPowerProjection_incl_ne {s t : ℕ} (h : s ≠ t)
    (p : symmetricPower t) : symmetricPowerProjection s ((symmetricPower t).incl p) = 0 := by
  apply Subtype.ext
  change MvPolynomial.homogeneousComponent s (p.val : Poly) = 0
  rw [MvPolynomial.homogeneousComponent_of_mem p.property,if_neg h]

/-- The corresponding actual relative homology projection kills every other coefficient degree. -/
theorem symmetricHomologyProjection_inclusion_ne {s t : ℕ} (h : s ≠ t)
    (z : TotalHomology (symmetricPower t)) :
    symmetricHomologyProjection s (symmetricHomologyInclusion t z) = 0 := by
  have hp : (symmetricPowerProjection s).comp (symmetricPower t).incl = 0 := by
    apply LieModuleHom.ext
    intro p
    exact symmetricPowerProjection_incl_ne h p
  have hh := congrArg coefficientTotalHomologyMap hp
  rw [coefficientTotalHomologyMap_comp,coefficientTotalHomologyMap_zero,
    coefficientTotalHomologyMap_symmetricPowerProjection,
    coefficientTotalHomologyMap_symmetricInclusion] at hh
  exact LinearMap.congr_fun hh z

/-- A literal root bidegree has its original symmetric coefficient degree. -/
def rootDegreeIndex (q r : ℕ) : RootHomologyDegrees (2*r+q) := ⟨(q,r),rfl⟩

/-- The inverse total homology model on one root block is the specified fixed-degree inclusion. -/
theorem strongTotalHomologyRootEquiv_symm_of (q r : ℕ) (x : RootHomologyModel q r) :
    strongTotalHomologyRootEquiv.symm
      (DirectSum.of (fun d : ℕ × ℕ => RootHomologyModel d.1 d.2) (q,r) x) =
        symmetricHomologyInclusion (2*r+q) ((symmetricPowerRootEquiv (2*r+q)).symm
          (DirectSum.of (fun d : RootHomologyDegrees (2*r+q) => RootHomologyModel d.val.1 d.val.2)
            (rootDegreeIndex q r) x)) := by
  apply strongTotalHomologyRootEquiv.symm_apply_eq.mpr
  rw [strongTotalHomologyRootEquiv_symmetricInclusion,LinearEquiv.apply_symm_apply,
    fixedRootInclusion_of]
  rfl

/-- The genuine total-degree projection preserves every root component of that degree. -/
theorem strongTotalHomologyRootEquiv_inclusion_projection (s : ℕ) (d : RootHomologyDegrees s)
    (h : TotalHomology SymmetricCoefficients) :
    strongTotalHomologyRootEquiv (symmetricHomologyInclusion s (symmetricHomologyProjection s h)) d.val =
      strongTotalHomologyRootEquiv h d.val := by
  obtain ⟨y,rfl⟩ := strongTotalHomologyRootEquiv.symm.surjective h
  induction y using DirectSum.induction_on with
  | zero => simp
  | add y z hy hz =>
    simp only [map_add]
    change strongTotalHomologyRootEquiv
      (symmetricHomologyInclusion s (symmetricHomologyProjection s (strongTotalHomologyRootEquiv.symm y))) d.val +
      strongTotalHomologyRootEquiv
      (symmetricHomologyInclusion s (symmetricHomologyProjection s (strongTotalHomologyRootEquiv.symm z))) d.val =
      strongTotalHomologyRootEquiv (strongTotalHomologyRootEquiv.symm y) d.val +
      strongTotalHomologyRootEquiv (strongTotalHomologyRootEquiv.symm z) d.val
    exact congrArg₂ (fun a b : RootHomologyModel d.val.1 d.val.2 => a+b) hy hz
  | of e x =>
    rw [LinearEquiv.apply_symm_apply,strongTotalHomologyRootEquiv_symm_of]
    by_cases hs : 2*e.2+e.1=s
    · cases hs
      rw [symmetricHomologyProjection_inclusion,strongTotalHomologyRootEquiv_symmetricInclusion,
        LinearEquiv.apply_symm_apply,fixedRootInclusion_of]
      rfl
    · rw [symmetricHomologyProjection_inclusion_ne (Ne.symm hs),map_zero,map_zero]
      have hd : d.val ≠ e := by
        intro he
        apply hs
        have hh := d.property
        rw [he] at hh
        exact hh
      change (0 : RootHomologyModel d.val.1 d.val.2) = _
      exact (DirectSum.of_eq_of_ne (β := fun d : ℕ × ℕ => RootHomologyModel d.1 d.2) e d.val x hd).symm

/-- Extract an actual root block of the full symmetric-coefficient homology. -/
def totalRootHomologyComponent (d : ℕ × ℕ) :
    TotalHomology SymmetricCoefficients →ₗ[ℂ] RootHomologyModel d.1 d.2 :=
  (DFinsupp.lapply d).comp strongTotalHomologyRootEquiv.toLinearMap

/-- Extract an actual root block from the fixed symmetric coefficient model. -/
def fixedRootHomologyComponent (s : ℕ) (d : RootHomologyDegrees s) :
    TotalHomology (symmetricPower s) →ₗ[ℂ] RootHomologyModel d.val.1 d.val.2 :=
  (DFinsupp.lapply d).comp (symmetricPowerRootEquiv s).toLinearMap

/-- The specified coefficient projection commutes with the explicit root component. -/
theorem fixedRootHomologyComponent_projection (s : ℕ) (d : RootHomologyDegrees s)
    (h : TotalHomology SymmetricCoefficients) :
    fixedRootHomologyComponent s d (symmetricHomologyProjection s h) =
      totalRootHomologyComponent d.val h := by
  have hh := strongTotalHomologyRootEquiv_inclusion_projection s d h
  rw [strongTotalHomologyRootEquiv_symmetricInclusion,fixedRootInclusion_apply] at hh
  exact hh

end KhanSL2.Macdonald
