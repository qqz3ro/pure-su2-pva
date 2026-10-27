module

public import KhanSL2.BGG.PolynomialKoszul

@[expose] public section

/-! Finite Koszul calculations and stabilization of the support cutoffs. -/
noncomputable section
open scoped BigOperators TensorProduct
open KhanSL2.FiniteExterior
namespace KhanSL2.BGG.PolynomialKoszul

/-- The number-operator identity for one creation/annihilation pair. -/
theorem dTerm_hTerm_apply (i j : Mode) (u : Chain) :
    dTerm i (hTerm j u) + hTerm j (dTerm i u) =
      if i=j then polynomialNumber i u + exteriorNumber i u else 0 := by
  have h := LinearMap.congr_fun (dTerm_hTerm i j) u
  by_cases hij : i=j
  · simpa only [if_pos hij, LinearMap.add_apply, LinearMap.comp_apply] using h
  · simpa only [if_neg hij, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] using h

theorem finite_euler (S : Finset Mode) (u : Chain) :
    finiteD S (finiteH S u) + finiteH S (finiteD S u) =
      ∑ i∈S, (polynomialNumber i u + exteriorNumber i u) := by
  simp only [finiteD_apply, finiteH_apply, map_sum]
  have hswap : (∑ j∈S, ∑ i∈S, dTerm i (hTerm j u)) =
      ∑ i∈S, ∑ j∈S, dTerm i (hTerm j u) := Finset.sum_comm
  rw [hswap, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  simp only [dTerm_hTerm_apply]
  simp [hi]

/-- Every finite Koszul differential squares to zero. -/
theorem finiteD_square_zero (S : Finset Mode) (u : Chain) : finiteD S (finiteD S u) = 0 := by
  have hanti (i j : Mode) : dTerm i (dTerm j u) = -dTerm j (dTerm i u) :=
    LinearMap.congr_fun (dTerms_anticomm i j) u
  have hz : finiteD S (finiteD S u) = -finiteD S (finiteD S u) := by
    simp only [finiteD_apply, map_sum]
    have hswap : (∑ j∈S, ∑ i∈S, dTerm i (dTerm j u)) =
        ∑ i∈S, ∑ j∈S, dTerm i (dTerm j u) := Finset.sum_comm
    rw [hswap]
    calc
      (∑ i∈S, ∑ j∈S, dTerm i (dTerm j u)) =
          ∑ i∈S, ∑ j∈S, -dTerm j (dTerm i u) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            exact hanti i j
      _ = -(∑ i∈S, ∑ j∈S, dTerm j (dTerm i u)) := by
        simp only [Finset.sum_neg_distrib]
      _ = _ := congrArg Neg.neg Finset.sum_comm
  have htwo : (2 : ℂ) • finiteD S (finiteD S u) = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp hz
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The finite Euler homotopies square to zero as well. -/
theorem finiteH_square_zero (S : Finset Mode) (u : Chain) : finiteH S (finiteH S u) = 0 := by
  have hanti (i j : Mode) : hTerm i (hTerm j u) = -hTerm j (hTerm i u) :=
    LinearMap.congr_fun (hTerms_anticomm i j) u
  have hz : finiteH S (finiteH S u) = -finiteH S (finiteH S u) := by
    simp only [finiteH_apply, map_sum]
    have hswap : (∑ j∈S, ∑ i∈S, hTerm i (hTerm j u)) =
        ∑ i∈S, ∑ j∈S, hTerm i (hTerm j u) := Finset.sum_comm
    rw [hswap]
    calc
      (∑ i∈S, ∑ j∈S, hTerm i (hTerm j u)) =
          ∑ i∈S, ∑ j∈S, -hTerm j (hTerm i u) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            exact hanti i j
      _ = -(∑ i∈S, ∑ j∈S, hTerm j (hTerm i u)) := by
        simp only [Finset.sum_neg_distrib]
      _ = _ := congrArg Neg.neg Finset.sum_comm
  have htwo : (2 : ℂ) • finiteH S (finiteH S u) = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp hz
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem dTerm_basis_zero (i : Mode) (b : BasisIndex) (hi : i∉b.2) :
    dTerm i (basis b) = 0 := by
  obtain ⟨s,t⟩ := b
  simp only [basis_apply, dTerm_tmul, PositiveCE.contract, contraction_monomial,
    if_neg hi, TensorProduct.tmul_zero]

theorem hTerm_basis_zero (i : Mode) (b : BasisIndex) (hi : i∉b.1.support) :
    hTerm i (basis b) = 0 := by
  obtain ⟨s,t⟩ := b
  have hz : s i = 0 := Finsupp.notMem_support_iff.mp hi
  simp only [basis_apply, hTerm_tmul, MvPolynomial.pderiv_monomial, hz, Nat.cast_zero,
    mul_zero, map_zero, TensorProduct.zero_tmul]

theorem finiteD_basis_eq (S : Finset Mode) (b : BasisIndex) (hb : b.2 ⊆ S) :
    finiteD S (basis b) = d (basis b) := by
  rw [finiteD_apply, d_basis]
  symm
  exact Finset.sum_subset hb (fun i _ hi => dTerm_basis_zero i b hi)

theorem finiteH_basis_eq (S : Finset Mode) (b : BasisIndex) (hb : b.1.support ⊆ S) :
    finiteH S (basis b) = H (basis b) := by
  rw [finiteH_apply, H_basis]
  symm
  exact Finset.sum_subset hb (fun i _ hi => hTerm_basis_zero i b hi)

/-- The variables occurring in a basis monomial. -/
def basisVariables (b : BasisIndex) : Finset Mode := b.1.support ∪ b.2

/-- A finite variable set supporting an arbitrary polynomial exterior chain. -/
def variableSupport (u : Chain) : Finset Mode := (basis.repr u).support.biUnion basisVariables

theorem eq_sum_basis (u : Chain) :
    u = ∑ b∈(basis.repr u).support, basis.repr u b • basis b := by
  symm
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using basis.linearCombination_repr u

theorem finiteD_eq (S : Finset Mode) (u : Chain) (hu : variableSupport u ⊆ S) :
    finiteD S u = d u := by
  rw [eq_sum_basis u]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [finiteD_basis_eq S b]
  intro i hi
  apply hu
  exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_union_right _ hi⟩

theorem finiteH_eq (S : Finset Mode) (u : Chain) (hu : variableSupport u ⊆ S) :
    finiteH S u = H u := by
  rw [eq_sum_basis u]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [finiteH_basis_eq S b]
  intro i hi
  apply hu
  exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_union_left _ hi⟩

/-- The actual differential squares to zero; one cutoff contains both inputs. -/
theorem d_square_zero (u : Chain) : d (d u) = 0 := by
  let S := variableSupport u ∪ variableSupport (d u)
  rw [← finiteD_eq S (d u) Finset.subset_union_right,
    ← finiteD_eq S u Finset.subset_union_left]
  exact finiteD_square_zero S u

/-- The actual unnormalized homotopy squares to zero. -/
theorem H_square_zero (u : Chain) : H (H u) = 0 := by
  let S := variableSupport u ∪ variableSupport (H u)
  rw [← finiteH_eq S (H u) Finset.subset_union_right,
    ← finiteH_eq S u Finset.subset_union_left]
  exact finiteH_square_zero S u

private theorem exterior_diagonal (i : Mode) (t : Finset Mode) :
    FiniteExterior.generator i * PositiveCE.contract i (monomial t) =
      if i∈t then monomial t else 0 := by
  by_cases hi : i∈t
  · simp only [PositiveCE.contract, contraction_monomial, if_pos hi, mul_smul_comm]
    change ((-1 : ℂ) ^ FiniteExterior.position PositiveCE.Mode.code i t) •
      FiniteExterior.wedge PositiveCE.Mode.code (FiniteExterior.generator i) (monomial (t.erase i)) = _
    rw [wedge_generator_monomial PositiveCE.Mode.code i (t.erase i) (Finset.notMem_erase i t),
      position_erase_self, Finset.insert_erase hi, smul_smul, sign_mul_self, one_smul]
  · simp [PositiveCE.contract, contraction_monomial, hi]

theorem polynomialNumber_sum_basis (S : Finset Mode) (s : Exponent) (t : Finset Mode)
    (hs : s.support ⊆ S) :
    (∑ i∈S, polynomialNumber i (basis (s,t))) =
      ((s.sum (fun _ n => n) : ℕ) : ℂ) • basis (s,t) := by
  simp only [basis_apply, polynomialNumber_tmul, MvPolynomial.X_mul_pderiv_monomial,
    ← TensorProduct.smul_tmul', ← Finset.sum_smul]
  have hsum : (∑ i∈S, s i) = s.sum (fun _ n => n) := by
    change (∑ i∈S, s i) = ∑ i∈s.support, s i
    symm
    exact Finset.sum_subset hs (fun i _ hi => Finsupp.notMem_support_iff.mp hi)
  rw [hsum, Nat.cast_smul_eq_nsmul ℂ]

theorem exteriorNumber_sum_basis (S : Finset Mode) (s : Exponent) (t : Finset Mode)
    (ht : t ⊆ S) :
    (∑ i∈S, exteriorNumber i (basis (s,t))) = (t.card : ℂ) • basis (s,t) := by
  simp only [basis_apply, exteriorNumber_tmul, exterior_diagonal, TensorProduct.tmul_ite,
    TensorProduct.tmul_zero]
  calc
    (∑ i∈S, if i∈t then MvPolynomial.monomial s (1 : ℂ) ⊗ₜ[ℂ] monomial t else 0) =
        ∑ i∈t, if i∈t then MvPolynomial.monomial s (1 : ℂ) ⊗ₜ[ℂ] monomial t else 0 := by
          symm
          exact Finset.sum_subset ht (fun i _ hi => by simp [hi])
    _ = (t.card : ℂ) • (MvPolynomial.monomial s (1 : ℂ) ⊗ₜ[ℂ] monomial t) := by
      simp [Nat.cast_smul_eq_nsmul]

/-- The finite number operator is total polynomial-plus-exterior length. -/
theorem finite_euler_basis (S : Finset Mode) (b : BasisIndex) (hb : basisVariables b ⊆ S) :
    finiteD S (finiteH S (basis b)) + finiteH S (finiteD S (basis b)) =
      (totalLength b : ℂ) • basis b := by
  obtain ⟨s,t⟩ := b
  rw [finite_euler, Finset.sum_add_distrib,
    polynomialNumber_sum_basis S s t (Finset.subset_union_left.trans hb),
    exteriorNumber_sum_basis S s t (Finset.subset_union_right.trans hb)]
  simp only [totalLength, Nat.cast_add, add_smul]

/-- The global Euler anticommutator, with no cutoff parameter or support hypothesis. -/
theorem euler_basis (b : BasisIndex) :
    d (H (basis b)) + H (d (basis b)) = (totalLength b : ℂ) • basis b := by
  let S := basisVariables b ∪ variableSupport (H (basis b)) ∪ variableSupport (d (basis b))
  have hb : basisVariables b ⊆ S := Finset.subset_union_left.trans Finset.subset_union_left
  rw [← finiteD_eq S (H (basis b)) (Finset.subset_union_right.trans Finset.subset_union_left),
    ← finiteH_eq S (d (basis b)) Finset.subset_union_right,
    ← finiteH_basis_eq S b (Finset.subset_union_left.trans hb),
    ← finiteD_basis_eq S b (Finset.subset_union_right.trans hb)]
  exact finite_euler_basis S b hb

end KhanSL2.BGG.PolynomialKoszul
