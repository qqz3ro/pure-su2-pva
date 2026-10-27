module

public import KhanSL2.BGG.PolynomialKoszulHomotopy
public import KhanSL2.BGG.ColorRootGrading

@[expose] public section

/-! Exterior degree and total length of the explicit polynomial Koszul contraction. -/
noncomputable section
open scoped BigOperators TensorProduct
open KhanSL2.FiniteExterior
namespace KhanSL2.BGG.PolynomialKoszul

theorem exteriorDegree_monomial (t : Finset Mode) :
    PositiveCE.degreeOp (monomial t) = (t.card : ℂ) • monomial t := by
  simpa only [PositiveCE.degreeOp, Finset.sum_const, nsmul_eq_mul, mul_one] using
    euler_monomial (fun _ : Mode => (1 : ℂ)) t

private theorem exteriorDegree_generator_mul (i : Mode) (u : Exterior) :
    PositiveCE.degreeOp (FiniteExterior.generator i * u) =
      FiniteExterior.generator i * u + FiniteExterior.generator i * PositiveCE.degreeOp u := by
  unfold PositiveCE.degreeOp
  rw [euler_mul, euler_generator, one_smul]

theorem exteriorDegree_contract (i : Mode) (u : Exterior) :
    PositiveCE.degreeOp (PositiveCE.contract i u) + PositiveCE.contract i u =
      PositiveCE.contract i (PositiveCE.degreeOp u) := by
  have heq : PositiveCE.degreeOp.comp (PositiveCE.contract i) + PositiveCE.contract i =
      (PositiveCE.contract i).comp PositiveCE.degreeOp := by
    apply (Finsupp.basisSingleOne : Module.Basis (Finset Mode) ℂ Exterior).ext
    intro t
    change PositiveCE.degreeOp (PositiveCE.contract i (monomial t)) +
      PositiveCE.contract i (monomial t) = PositiveCE.contract i (PositiveCE.degreeOp (monomial t))
    by_cases hi : i∈t
    · simp only [exteriorDegree_monomial, map_smul, PositiveCE.contract,
        contraction_monomial, if_pos hi]
      rw [← Finset.card_erase_add_one hi]
      simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul, smul_add]
      module
    · simp [exteriorDegree_monomial, PositiveCE.contract, contraction_monomial, hi]
  exact LinearMap.congr_fun heq u

/-- Exterior degree on the tensor module. -/
def exteriorDegree : Module.End ℂ Chain := TensorProduct.map LinearMap.id PositiveCE.degreeOp

@[simp] theorem exteriorDegree_tmul (p : Poly) (u : Exterior) :
    exteriorDegree (p ⊗ₜ[ℂ] u) = p ⊗ₜ[ℂ] PositiveCE.degreeOp u := rfl

@[simp] theorem exteriorDegree_basis (b : BasisIndex) :
    exteriorDegree (basis b) = (b.2.card : ℂ) • basis b := by
  obtain ⟨s,t⟩ := b
  simp only [basis_apply, exteriorDegree_tmul, exteriorDegree_monomial, TensorProduct.tmul_smul]

theorem exteriorDegree_eq_weighted : exteriorDegree = weighted (fun b => (b.2.card : ℂ)) := by
  apply basis.ext
  intro b
  rw [exteriorDegree_basis, weighted_basis]

private theorem exteriorDegree_dTerm (i : Mode) (u : Chain) :
    exteriorDegree (dTerm i u) + dTerm i u = dTerm i (exteriorDegree u) := by
  have heq : exteriorDegree.comp (dTerm i) + dTerm i = (dTerm i).comp exteriorDegree := by
    apply TensorProduct.ext'
    intro p v
    simp only [LinearMap.add_apply, LinearMap.comp_apply, dTerm_tmul, exteriorDegree_tmul]
    rw [← TensorProduct.tmul_add, exteriorDegree_contract]
  exact LinearMap.congr_fun heq u

private theorem exteriorDegree_hTerm (i : Mode) (u : Chain) :
    exteriorDegree (hTerm i u) = hTerm i (exteriorDegree u) + hTerm i u := by
  have heq : exteriorDegree.comp (hTerm i) = (hTerm i).comp exteriorDegree + hTerm i := by
    apply TensorProduct.ext'
    intro p v
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hTerm_tmul, exteriorDegree_tmul,
      exteriorDegree_generator_mul, TensorProduct.tmul_add]
    abel
  exact LinearMap.congr_fun heq u

theorem exteriorDegree_d (u : Chain) : exteriorDegree (d u) + d u = d (exteriorDegree u) := by
  let S := variableSupport u ∪ variableSupport (exteriorDegree u)
  rw [← finiteD_eq S u Finset.subset_union_left,
    ← finiteD_eq S (exteriorDegree u) Finset.subset_union_right]
  simp only [finiteD_apply, map_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact exteriorDegree_dTerm i u

theorem exteriorDegree_H (u : Chain) : exteriorDegree (H u) = H (exteriorDegree u) + H u := by
  let S := variableSupport u ∪ variableSupport (exteriorDegree u)
  rw [← finiteH_eq S u Finset.subset_union_left,
    ← finiteH_eq S (exteriorDegree u) Finset.subset_union_right]
  simp only [finiteH_apply, map_sum, exteriorDegree_hTerm, Finset.sum_add_distrib]

theorem exteriorDegree_inverseLength (u : Chain) :
    exteriorDegree (inverseLength u) = inverseLength (exteriorDegree u) := by
  have heq : exteriorDegree.comp inverseLength = inverseLength.comp exteriorDegree := by
    apply basis.ext
    intro b
    simp only [LinearMap.comp_apply, inverseLength_basis, exteriorDegree_basis, map_smul,
      smul_smul, mul_comm]
  exact LinearMap.congr_fun heq u

theorem exteriorDegree_homotopy (u : Chain) :
    exteriorDegree (homotopy u) = homotopy (exteriorDegree u) + homotopy u := by
  simp only [homotopy, LinearMap.comp_apply, exteriorDegree_H, exteriorDegree_inverseLength]

/-- Exterior degree p, stated by actual finite basis support. -/
def degreePiece (p : ℕ) : Submodule ℂ Chain :=
  (Finsupp.supported ℂ ℂ {b : BasisIndex | b.2.card=p}).comap basis.repr.toLinearMap

/-- Total polynomial-plus-exterior length n. -/
def lengthPiece (n : ℕ) : Submodule ℂ Chain :=
  (Finsupp.supported ℂ ℂ {b : BasisIndex | totalLength b=n}).comap basis.repr.toLinearMap

theorem mem_degreePiece_iff (u : Chain) (p : ℕ) :
    u∈degreePiece p ↔ exteriorDegree u = (p : ℂ) • u := by
  change (∀ b∈(basis.repr u).support, b.2.card=p) ↔ _
  rw [exteriorDegree_eq_weighted, weighted_eigen_iff]
  simp only [Nat.cast_inj]

theorem mem_lengthPiece_iff (u : Chain) (n : ℕ) :
    u∈lengthPiece n ↔ lengthOp u = (n : ℂ) • u := by
  change (∀ b∈(basis.repr u).support, totalLength b=n) ↔ _
  rw [lengthOp, weighted_eigen_iff]
  simp only [Nat.cast_inj]

theorem d_mem_degreePiece {p : ℕ} {u : Chain} (hu : u∈degreePiece (p+1)) :
    d u∈degreePiece p := by
  rw [mem_degreePiece_iff] at hu ⊢
  have h := exteriorDegree_d u
  rw [hu, map_smul] at h
  simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul] at h
  exact add_right_cancel h

theorem homotopy_mem_degreePiece {p : ℕ} {u : Chain} (hu : u∈degreePiece p) :
    homotopy u∈degreePiece (p+1) := by
  rw [mem_degreePiece_iff] at hu ⊢
  rw [exteriorDegree_homotopy, hu, map_smul]
  simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]

theorem d_mem_lengthPiece {n : ℕ} {u : Chain} (hu : u∈lengthPiece n) : d u∈lengthPiece n := by
  rw [mem_lengthPiece_iff] at hu ⊢
  rw [lengthOp_d, hu, map_smul]

theorem homotopy_mem_lengthPiece {n : ℕ} {u : Chain} (hu : u∈lengthPiece n) :
    homotopy u∈lengthPiece n := by
  rw [mem_lengthPiece_iff] at hu ⊢
  rw [lengthOp_homotopy, hu, map_smul]

/-- The actual homogeneous primitive needed for filtered leading-cycle correction. -/
theorem homogeneous_preimage {p n : ℕ} {u : Chain}
    (hp : u∈degreePiece p) (hn : u∈lengthPiece n)
    (hd : d u=0) (ha : augmentation u=0) :
    ∃ v∈degreePiece (p+1), v∈lengthPiece n ∧ d v=u :=
  ⟨homotopy u, homotopy_mem_degreePiece hp, homotopy_mem_lengthPiece hn,
    preimage_of_augmented_cycle u hd ha⟩


/-- Positive exterior degree has zero scalar augmentation. -/
theorem augmentation_eq_zero_of_positive_degree {p : ℕ} {u : Chain}
    (hu : u∈degreePiece (p+1)) : augmentation u=0 := by
  change ∀ b∈(basis.repr u).support, b.2.card=p+1 at hu
  by_contra h
  have hb : scalarIndex∈(basis.repr u).support := Finsupp.mem_support_iff.mpr h
  have hcard := hu scalarIndex hb
  simp [scalarIndex] at hcard

/-- The Koszul differential vanishes in exterior degree zero. -/
theorem d_eq_zero_of_degree_zero {u : Chain} (hu : u∈degreePiece 0) : d u=0 := by
  change ∀ b∈(basis.repr u).support, b.2.card=0 at hu
  rw [eq_sum_basis u]
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro b hb
  rw [d_basis, Finset.card_eq_zero.mp (hu b hb)]
  simp

/-- Positive-degree Koszul cycles have homogeneous primitives one degree higher. -/
theorem positive_homogeneous_preimage {p n : ℕ} {u : Chain}
    (hp : u∈degreePiece (p+1)) (hn : u∈lengthPiece n) (hd : d u=0) :
    ∃ v∈degreePiece (p+2), v∈lengthPiece n ∧ d v=u :=
  homogeneous_preimage hp hn hd (augmentation_eq_zero_of_positive_degree hp)

/-- In degree zero, every homogeneous augmentation-kernel element is a boundary. -/
theorem augmentation_kernel_homogeneous_preimage {n : ℕ} {u : Chain}
    (hp : u∈degreePiece 0) (hn : u∈lengthPiece n) (ha : augmentation u=0) :
    ∃ v∈degreePiece 1, v∈lengthPiece n ∧ d v=u :=
  homogeneous_preimage hp hn (d_eq_zero_of_degree_zero hp) ha

end KhanSL2.BGG.PolynomialKoszul
