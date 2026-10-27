module

public import KhanSL2.Modules.CoefficientOperators

@[expose] public section

/-! # Coefficient power sums raise spin and act on actual homology -/

noncomputable section
open scoped TensorProduct DirectSum

namespace KhanSL2.Modules

open Current LieChains

/-- The loop-degree commutator records the degree of multiplication by `z^m`. -/
theorem eulerCoeff_coefficientShift_commutator (m : ℕ) :
    eulerCoeff * coefficientShift m - coefficientShift m * eulerCoeff =
      (m : ℂ) • coefficientShift m := by
  apply curBasis.ext
  rintro ⟨j, a⟩
  simp only [curBasis_apply', LinearMap.sub_apply, Module.End.mul_apply,
    coefficientShift_cur, eulerCoeff, LinearMap.add_apply, Module.End.one_apply,
    eulerCur_cur, map_add, map_smul, LinearMap.smul_apply]
  simp only [Nat.cast_add, add_smul]
  abel

/-- The same commutator on the exterior coefficient module. -/
theorem eulerCoeff_coefficientPower (m : ℕ) (v : NB) :
    derivExt eulerCoeff (coefficientPower m v) =
      coefficientPower m (derivExt eulerCoeff v) + (m : ℂ) • coefficientPower m v := by
  have h := derivExt_commutator eulerCoeff (coefficientShift m) v
  rw [eulerCoeff_coefficientShift_commutator, derivExt_smul] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

/-- Coefficient power sums do not change the number of Lie algebra factors. -/
theorem formDegree_coefficientChainPower (m : ℕ) (ξ : GenChains) :
    formDegree (coefficientChainPower m ξ) = coefficientChainPower m (formDegree ξ) := by
  exact (coefficientChainPower_lieDeriv m 1 0 (Commute.zero_right _) ξ).symm

/-- Coefficient power sums do not change coefficient exterior degree. -/
theorem coeffDegree_coefficientChainPower (m : ℕ) (ξ : GenChains) :
    coeffDegree (coefficientChainPower m ξ) = coefficientChainPower m (coeffDegree ξ) := by
  apply (coefficientChainPower_lieDeriv m 0 (derivExt 1) _ ξ).symm
  exact derivExt_commute (Commute.one_right _)

/-- The operator attached to `p_m` raises spin by `m`. -/
theorem spin_coefficientChainPower (m : ℕ) (ξ : GenChains) :
    spin (coefficientChainPower m ξ) =
      coefficientChainPower m (spin ξ) + (m : ℂ) • coefficientChainPower m ξ := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    simp only [coefficientChainPower_tmul, spin, lieDeriv_tmul, map_add,
      eulerCoeff_coefficientPower, TensorProduct.tmul_add, TensorProduct.tmul_smul]
    abel
  | add ξ η hξ hη => simp only [map_add, hξ, hη, smul_add]; abel

/-- The intrinsic joint-eigenspace grading is preserved, with the specified spin shift. -/
theorem coefficientChainPower_mem_piece (m p B : ℕ) (S : ℤ) {ξ : GenChains}
    (hξ : ξ ∈ genPiece (kDegree p B S)) :
    coefficientChainPower m ξ ∈ genPiece (kDegree p B (S + m)) := by
  rcases (mem_kPiece_iff p B S ξ).mp hξ with ⟨hp, hB, hS⟩
  apply (mem_kPiece_iff p B (S + m) (coefficientChainPower m ξ)).mpr
  refine ⟨?_, ?_, ?_⟩
  · rw [formDegree_coefficientChainPower, hp, map_smul]
  · rw [coeffDegree_coefficientChainPower, hB, map_smul]
  · simp only [spin_coefficientChainPower, hS, map_smul, Int.cast_add,
      Int.cast_natCast, add_smul]

/-- The shifted spin statement descends to relative chains. -/
theorem coefficientRelPower_mem_piece (m p B : ℕ) (S : ℤ) {x : RelChains}
    (hx : x ∈ relPiece (kDegree p B S)) :
    coefficientRelPower m x ∈ relPiece (kDegree p B (S + m)) := by
  obtain ⟨ξ, hξ, rfl⟩ := hx
  exact ⟨coefficientChainPower m ξ, coefficientChainPower_mem_piece m p B S hξ, rfl⟩

theorem coefficientRelPower_mem_cycles (m p B : ℕ) (S : ℤ) {x : RelChains}
    (hx : x ∈ relCycles (kDegree p B S)) :
    coefficientRelPower m x ∈ relCycles (kDegree p B (S + m)) := by
  refine ⟨coefficientRelPower_mem_piece m p B S hx.1, ?_⟩
  change relBoundary (coefficientRelPower m x) = 0
  rw [relBoundary_coefficientRelPower, hx.2, map_zero]

theorem kDegree_next (p B : ℕ) (S : ℤ) :
    kDegree p B S + (1, 0, 0) = kDegree (p + 1) B S := by
  simp [kDegree, Nat.cast_add, add_assoc]

/-- Boundaries are carried to boundaries with the same spin shift. -/
theorem coefficientRelPower_mem_boundaries (m p B : ℕ) (S : ℤ) {x : RelChains}
    (hx : x ∈ relBoundaries (kDegree p B S)) :
    coefficientRelPower m x ∈ relBoundaries (kDegree p B (S + m)) := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨coefficientRelPower m y, ?_, ?_⟩
  · rw [kDegree_next] at hy ⊢
    exact coefficientRelPower_mem_piece m (p + 1) B S hy
  · exact relBoundary_coefficientRelPower m y

/-- The specified map on relative cycles. -/
def coefficientCyclesPower (m p B : ℕ) (S : ℤ) :
    relCycles (kDegree p B S) →ₗ[ℂ] relCycles (kDegree p B (S + m)) :=
  LinearMap.codRestrict _ ((coefficientRelPower m).comp (relCycles (kDegree p B S)).subtype)
    (fun x => coefficientRelPower_mem_cycles m p B S x.property)

/-- The coefficient power sum on the actual homology `K p B S`. -/
def coefficientKPower (m p B : ℕ) (S : ℤ) : K p B S →ₗ[ℂ] K p B (S + m) :=
  ((relBoundaries (kDegree p B S)).comap (relCycles (kDegree p B S)).subtype).mapQ
    ((relBoundaries (kDegree p B (S + m))).comap
      (relCycles (kDegree p B (S + m))).subtype)
    (coefficientCyclesPower m p B S)
    (fun _ hx => coefficientRelPower_mem_boundaries m p B S hx)

/-- A relative cycle represents its actual homology class. -/
def coefficientClass (p B : ℕ) (S : ℤ) (x : RelChains)
    (hx : x ∈ relCycles (kDegree p B S)) : K p B S :=
  ((relBoundaries (kDegree p B S)).comap (relCycles (kDegree p B S)).subtype).mkQ ⟨x, hx⟩

@[simp] theorem coefficientKPower_class (m p B : ℕ) (S : ℤ) (x : RelChains)
    (hx : x ∈ relCycles (kDegree p B S)) :
    coefficientKPower m p B S (coefficientClass p B S x hx) =
      coefficientClass p B (S + m) (coefficientRelPower m x)
        (coefficientRelPower_mem_cycles m p B S hx) := rfl

/-- Power sums on the algebraic direct sum of the actual spin-graded homology. -/
def coefficientTotalPower (m B p : ℕ) : Module.End ℂ (KTotal B p) :=
  DirectSum.toModule ℂ ℤ (KTotal B p) fun S =>
    (DirectSum.lof ℂ ℤ (fun T => K p B T) (S + m)).comp (coefficientKPower m p B S)

@[simp] theorem coefficientTotalPower_lof (m B p : ℕ) (S : ℤ) (x : K p B S) :
    coefficientTotalPower m B p (DirectSum.lof ℂ ℤ (fun T => K p B T) S x) =
      DirectSum.lof ℂ ℤ (fun T => K p B T) (S + m) (coefficientKPower m p B S x) :=
  DirectSum.toModule_lof ℂ S x

/-- The specified homogeneous cycle in the assembled homology. -/
def coefficientTotalClass (p B : ℕ) (S : ℤ) (x : RelChains)
    (hx : x ∈ relCycles (kDegree p B S)) : KTotal B p :=
  DirectSum.lof ℂ ℤ (fun T => K p B T) S (coefficientClass p B S x hx)

@[simp] theorem coefficientTotalPower_class (m B p : ℕ) (S : ℤ) (x : RelChains)
    (hx : x ∈ relCycles (kDegree p B S)) :
    coefficientTotalPower m B p (coefficientTotalClass p B S x hx) =
      coefficientTotalClass p B (S + m) (coefficientRelPower m x)
        (coefficientRelPower_mem_cycles m p B S hx) := by
  simp only [coefficientTotalClass, coefficientTotalPower_lof, coefficientKPower_class]

theorem coefficientTotalClass_congr (p B : ℕ) {S T : ℤ} {x y : RelChains}
    (hST : S = T) (hxy : x = y)
    (hx : x ∈ relCycles (kDegree p B S)) (hy : y ∈ relCycles (kDegree p B T)) :
    coefficientTotalClass p B S x hx = coefficientTotalClass p B T y hy := by
  subst T
  subst y
  rfl

theorem coefficientClass_surjective (p B : ℕ) (S : ℤ) :
    Function.Surjective (fun x : relCycles (kDegree p B S) =>
      coefficientClass p B S x x.property) :=
  ((relBoundaries (kDegree p B S)).comap (relCycles (kDegree p B S)).subtype).mkQ_surjective

/-- Commutation on a specified homogeneous relative cycle. -/
theorem coefficientTotalPower_commute_class (m n B p : ℕ) (S : ℤ) (v : RelChains)
    (hv : v ∈ relCycles (kDegree p B S)) :
    coefficientTotalPower m B p
        (coefficientTotalPower n B p (coefficientTotalClass p B S v hv)) =
      coefficientTotalPower n B p
        (coefficientTotalPower m B p (coefficientTotalClass p B S v hv)) := by
  simp only [coefficientTotalPower_class]
  have hS : S + (n : ℤ) + m = S + (m : ℤ) + n := by omega
  have hv' := LinearMap.congr_fun (coefficientRelPower_commute m n).eq v
  exact coefficientTotalClass_congr p B hS hv' _ _

/-- Commutation on each homogeneous inclusion. -/
theorem coefficientTotalPower_commute_lof (m n B p : ℕ) (S : ℤ) (x : K p B S) :
    coefficientTotalPower m B p
        (coefficientTotalPower n B p (DirectSum.lof ℂ ℤ (fun T => K p B T) S x)) =
      coefficientTotalPower n B p
        (coefficientTotalPower m B p (DirectSum.lof ℂ ℤ (fun T => K p B T) S x)) := by
  refine Submodule.Quotient.induction_on
    (p := (relBoundaries (kDegree p B S)).comap (relCycles (kDegree p B S)).subtype)
    x (fun v => ?_)
  exact coefficientTotalPower_commute_class m n B p S v v.property

/-- The descended power sums still commute, including their spin shifts. -/
theorem coefficientTotalPower_commute (m n B p : ℕ) :
    Commute (coefficientTotalPower m B p) (coefficientTotalPower n B p) :=
  DirectSum.linearMap_ext (R := ℂ) (M := fun S : ℤ => K p B S)
    (fun S => LinearMap.ext (coefficientTotalPower_commute_lof m n B p S))

end KhanSL2.Modules