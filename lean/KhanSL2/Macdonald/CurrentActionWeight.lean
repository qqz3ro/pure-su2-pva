module

public import KhanSL2.Macdonald.CurrentActionDegree
public import KhanSL2.Macdonald.Grading

@[expose] public section

/-! Current modes and coefficient shifts have their actual positive weight shifts
on the symmetric chain coefficients. Even polynomial zero modes are included. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.Macdonald

/-- A derivation is homogeneous of shift j when this holds on every polynomial variable. -/
theorem polynomialDerivation_shifts_weight (D : Derivation ℂ Poly Poly)
    (wt : Mode → ℕ) (j : ℕ)
    (hX : ∀ m : Mode, D (MvPolynomial.X m) ∈
      MvPolynomial.weightedHomogeneousSubmodule ℂ wt (wt m + j))
    {w : ℕ} {p : Poly} (hp : p ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ wt w) :
    D p ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ wt (w+j) := by
  have hD : D = MvPolynomial.mkDerivation ℂ (fun m => D (MvPolynomial.X m)) := by
    apply MvPolynomial.derivation_ext
    intro m
    simp
  rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single] at hp
  refine Submodule.span_induction ?_ ?_
    (fun u v _ _ hu hv => ?_) (fun c u _ hu => ?_) hp
  · rintro _ ⟨d,hd,rfl⟩
    change D (MvPolynomial.monomial d 1) ∈ _
    rw [hD, MvPolynomial.mkDerivation_monomial, one_smul]
    change ∑ m ∈ d.support, MvPolynomial.monomial (d - Finsupp.single m 1)
      (d m : ℂ) * D (MvPolynomial.X m) ∈ _
    apply Submodule.sum_mem
    intro m hm
    have hweight : Finsupp.weight wt (d-Finsupp.single m 1) + (wt m+j) = w+j := by
      rw [← add_assoc, Finsupp.weight_sub_single_add (Finsupp.mem_support_iff.mp hm)]
      exact congrArg (fun n : ℕ => n+j) hd
    have hmon := MvPolynomial.isWeightedHomogeneous_monomial wt
      (d-Finsupp.single m 1) (d m : ℂ) rfl
    change MvPolynomial.IsWeightedHomogeneous wt _ (w+j)
    rw [← hweight]
    exact hmon.mul (hX m)
  · simp
  · rw [map_add]
    exact Submodule.add_mem _ hu hv
  · rw [Derivation.map_smul]
    exact Submodule.smul_mem _ c hu

/-- Weight on polynomial exponents agrees with the mixed-algebra grading. -/
theorem polynomialWeight_eq_finsuppWeight (d : Exponent) :
    polynomialWeight d = Finsupp.weight BGG.PositiveCE.Mode.index d := by
  simp only [polynomialWeight, Finsupp.weight_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro m _
  simp [nsmul_eq_mul, Nat.mul_comm]

/-- A homogeneous weight submodule of the symmetric polynomial coefficients. -/
def polynomialWeightPiece (w : ℕ) : Submodule ℂ Poly :=
  MvPolynomial.weightedHomogeneousSubmodule ℂ BGG.PositiveCE.Mode.index w

theorem mem_polynomialWeightPiece (w : ℕ) (p : Poly) :
    p ∈ polynomialWeightPiece w ↔ ∀ d ∈ p.support, polynomialWeight d = w := by
  simp only [polynomialWeightPiece, MvPolynomial.mem_weightedHomogeneousSubmodule,
    MvPolynomial.IsWeightedHomogeneous, MvPolynomial.mem_support_iff,
    polynomialWeight_eq_finsuppWeight]

/-- A current of mode j raises symmetric-coefficient weight by j. -/
theorem currentAction_mode_mem_weight (j : ℕ) (a : Fin 3) {w : ℕ} {p : Poly}
    (hp : p ∈ polynomialWeightPiece w) :
    currentAction (BGG.mode j (MatrixSL2.color a)) p ∈ polynomialWeightPiece (w+j) := by
  apply polynomialDerivation_shifts_weight _ BGG.PositiveCE.Mode.index j _ hp
  rintro ⟨n,b⟩
  rw [currentAction_mode_X]
  apply Submodule.sum_mem
  intro c _
  apply Submodule.smul_mem
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
  simpa only [Nat.add_comm] using
    MvPolynomial.isWeightedHomogeneous_X ℂ BGG.PositiveCE.Mode.index (⟨j+n,c⟩ : Mode)

/-- The raising coefficient operator has exactly its advertised weight shift. -/
theorem symmetricCoefficientShift_mem_weight (m : ℕ) {w : ℕ} {p : Poly}
    (hp : p ∈ polynomialWeightPiece w) :
    symmetricCoefficientShift m p ∈ polynomialWeightPiece (w+m) := by
  apply polynomialDerivation_shifts_weight _ BGG.PositiveCE.Mode.index m _ hp
  rintro ⟨n,a⟩
  rw [symmetricCoefficientShift_X]
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
  simpa only [Nat.add_comm] using
    MvPolynomial.isWeightedHomogeneous_X ℂ BGG.PositiveCE.Mode.index (⟨m+n,a⟩ : Mode)

end KhanSL2.Macdonald
