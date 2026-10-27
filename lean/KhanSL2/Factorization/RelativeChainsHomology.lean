module

public import KhanSL2.Factorization.RelativeChainsComplex

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The categorical homology of the bundled relative CE complex is exactly
our explicit degreewise quotient of actual cycles by actual boundaries. -/

noncomputable section
open CategoryTheory
namespace KhanSL2.Factorization
open KhanSL2.BGG

variable (N : Type*) [AddCommGroup N] [Module ℂ N]
  [LieRingModule Current N] [LieModule ℂ Current N]

/-- The outgoing differential, including the zero-degree endpoint. -/
theorem complex_d_out_apply (j : ℕ) (z : degree N j) :
    ((complex N).d j (j - 1) z : degree N (j-1)).val = differential N z := by
  cases j with
  | zero =>
    rw [(complex N).shape 0 0 (show ¬ (ComplexShape.down ℕ).Rel 0 0 by simp)]
    exact (differential_eq_zero_of_degree_zero N z.property).symm
  | succ j =>
    simp only [Nat.add_one_sub_one]
    rw [complex_d]
    rfl

/-- The short complex with its predecessor and successor displayed explicitly. -/
abbrev degreeShortComplex (j : ℕ) : ShortComplex (ModuleCat ℂ) :=
  (complex N).sc' (j+1) j (j-1)

/-- Cycles in categorical homology have precisely the specified exterior degree
and vanish under the actual relative differential. -/
def degreeCycleEquiv (j : ℕ) :
    LinearMap.ker (degreeShortComplex N j).g.hom ≃ₗ[ℂ] (window N j).cycles where
  toFun z := ⟨(show degree N j from z.val).val, (show degree N j from z.val).property, by
    change differential N (show degree N j from z.val).val = 0
    rw [← complex_d_out_apply N j z.val]
    exact congrArg (fun w : degree N (j-1) => w.val) z.property⟩
  invFun z := ⟨⟨z.val, z.property.1⟩, by
    change (complex N).d j (j-1) ⟨z.val, z.property.1⟩ = 0
    apply Subtype.ext
    rw [complex_d_out_apply]
    exact z.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem degreeCycleEquiv_val (j : ℕ)
    (z : LinearMap.ker (degreeShortComplex N j).g.hom) :
    (degreeCycleEquiv N j z).val = (show degree N j from z.val).val := rfl

theorem degreeCycleEquiv_boundaries (j : ℕ) :
    (LinearMap.range (degreeShortComplex N j).moduleCatToCycles).map
      (degreeCycleEquiv N j).toLinearMap = (window N j).boundaries := by
  ext z
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨(show degree N (j+1) from w).val, (show degree N (j+1) from w).property, ?_⟩
    change differential N (show degree N (j+1) from w).val =
      ((complex N).d (j+1) j w : degree N j).val
    rw [complex_d]
    rfl
  · rintro ⟨w, hw, hwz⟩
    let w' : degree N (j+1) := ⟨w, hw⟩
    refine ⟨(degreeShortComplex N j).moduleCatToCycles w', ⟨w', rfl⟩, ?_⟩
    apply Subtype.ext
    change ((complex N).d (j+1) j w' : degree N j).val = z.val
    rw [complex_d]
    exact hwz

/-- The concrete quotient attached to a short complex is the actual relative
cycle/boundary quotient used throughout the project. -/
def degreeShortHomologyEquiv (j : ℕ) :
    (degreeShortComplex N j).moduleCatLeftHomologyData.H ≃ₗ[ℂ] Homology N j :=
  Submodule.Quotient.equiv _ _ (degreeCycleEquiv N j) (degreeCycleEquiv_boundaries N j)

/-- No substitute homology is introduced by bundling the actual relative chain
complex: its categorical homology is canonically the original quotient. -/
def complexHomologyEquiv (j : ℕ) : (complex N).homology j ≃ₗ[ℂ] Homology N j :=
  (((complex N).homologyIsoSc' (j+1) j (j-1) (ChainComplex.prev ℕ j) (by
    cases j with
    | zero => exact ChainComplex.next_nat_zero
    | succ j => simpa only [Nat.add_one_sub_one] using ChainComplex.next_nat_succ j
    )).toLinearEquiv.trans
      (degreeShortComplex N j).moduleCatHomologyIso.toLinearEquiv).trans
        (degreeShortHomologyEquiv N j)

end KhanSL2.Factorization

