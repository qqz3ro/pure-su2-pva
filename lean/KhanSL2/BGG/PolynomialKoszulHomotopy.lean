module

public import KhanSL2.BGG.PolynomialKoszulFinite

@[expose] public section

/-! The normalized polynomial Koszul homotopy and its actual augmented contraction. -/
noncomputable section
open scoped BigOperators TensorProduct
namespace KhanSL2.BGG.PolynomialKoszul

/-- A diagonal operator in the genuine tensor-monomial basis. -/
def weighted (f : BasisIndex → ℂ) : Module.End ℂ Chain :=
  basis.constr ℂ (fun b => f b • basis b)

@[simp] theorem weighted_basis (f : BasisIndex → ℂ) (b : BasisIndex) :
    weighted f (basis b) = f b • basis b := basis.constr_basis ℂ _ b

theorem weighted_repr (f : BasisIndex → ℂ) (u : Chain) (b : BasisIndex) :
    basis.repr (weighted f u) b = f b * basis.repr u b := by
  classical
  have heq : (Finsupp.lapply b).comp (basis.repr.toLinearMap.comp (weighted f)) =
      f b • (Finsupp.lapply b).comp basis.repr.toLinearMap := by
    apply basis.ext
    intro c
    simp only [LinearMap.comp_apply, weighted_basis, map_smul, Finsupp.smul_apply,
      smul_eq_mul, LinearMap.smul_apply, Module.Basis.repr_self_apply]
    by_cases h : c=b
    · subst c
      simp
    · simp [h]
  exact LinearMap.congr_fun heq u

/-- A diagonal eigenvector has exactly the corresponding basis support weights. -/
theorem weighted_eigen_iff (f : BasisIndex → ℂ) (c : ℂ) (u : Chain) :
    weighted f u = c • u ↔ ∀ b∈(basis.repr u).support, f b = c := by
  constructor
  · intro h b hb
    have hcoeff := congrArg (fun x => basis.repr x b) h
    simp only [weighted_repr, map_smul, Finsupp.smul_apply, smul_eq_mul] at hcoeff
    exact mul_right_cancel₀ (Finsupp.mem_support_iff.mp hb) hcoeff
  · intro h
    apply basis.ext_elem
    intro b
    rw [weighted_repr, map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases hb : b∈(basis.repr u).support
    · rw [h b hb]
    · simp only [Finsupp.notMem_support_iff.mp hb, mul_zero]
/-- Total polynomial-plus-exterior length as an actual diagonal operator. -/
def lengthOp : Module.End ℂ Chain := weighted (fun b => (totalLength b : ℂ))

@[simp] theorem lengthOp_basis (b : BasisIndex) :
    lengthOp (basis b) = (totalLength b : ℂ) • basis b := weighted_basis _ _

theorem lengthOp_repr (u : Chain) (b : BasisIndex) :
    basis.repr (lengthOp u) b = (totalLength b : ℂ) * basis.repr u b := weighted_repr _ _ _

/-- The full Euler identity, now as an equality of actual endomorphisms. -/
theorem lengthOp_eq : lengthOp = d.comp H + H.comp d := by
  apply basis.ext
  intro b
  simpa only [lengthOp_basis, LinearMap.add_apply, LinearMap.comp_apply] using (euler_basis b).symm

theorem lengthOp_d (u : Chain) : lengthOp (d u) = d (lengthOp u) := by
  simp only [lengthOp_eq, LinearMap.add_apply, LinearMap.comp_apply, d_square_zero,
    map_zero, map_add, zero_add, add_zero]

theorem lengthOp_H (u : Chain) : lengthOp (H u) = H (lengthOp u) := by
  simp only [lengthOp_eq, LinearMap.add_apply, LinearMap.comp_apply, H_square_zero,
    map_zero, map_add, zero_add, add_zero]

/-- Division by total length, with value zero on the scalar basis vector. -/
def inverseLength : Module.End ℂ Chain := weighted (fun b => (totalLength b : ℂ)⁻¹)

@[simp] theorem inverseLength_basis (b : BasisIndex) :
    inverseLength (basis b) = (totalLength b : ℂ)⁻¹ • basis b := weighted_basis _ _

theorem inverseLength_eq_of_eigen (u : Chain) (n : ℕ)
    (hu : lengthOp u = (n : ℂ) • u) : inverseLength u = (n : ℂ)⁻¹ • u := by
  classical
  apply basis.ext_elem
  intro b
  change basis.repr (weighted _ u) b = _
  rw [weighted_repr, map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases hc : basis.repr u b = 0
  · simp [hc]
  · have h := congrArg (fun x => basis.repr x b) hu
    simp only [lengthOp_repr, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
    rw [mul_right_cancel₀ hc h]

theorem inverseLength_d_basis (b : BasisIndex) :
    inverseLength (d (basis b)) = (totalLength b : ℂ)⁻¹ • d (basis b) := by
  apply inverseLength_eq_of_eigen
  rw [lengthOp_d, lengthOp_basis, map_smul]

theorem inverseLength_H_basis (b : BasisIndex) :
    inverseLength (H (basis b)) = (totalLength b : ℂ)⁻¹ • H (basis b) := by
  apply inverseLength_eq_of_eigen
  rw [lengthOp_H, lengthOp_basis, map_smul]

/-- The normalized Euler homotopy. -/
def homotopy : Module.End ℂ Chain := H.comp inverseLength

@[simp] theorem homotopy_basis (b : BasisIndex) :
    homotopy (basis b) = (totalLength b : ℂ)⁻¹ • H (basis b) := by
  simp only [homotopy, LinearMap.comp_apply, inverseLength_basis, map_smul]

/-- The unique basis index of total length zero. -/
def scalarIndex : BasisIndex := (0, ∅)

theorem totalLength_zero_iff (b : BasisIndex) : totalLength b = 0 ↔ b = scalarIndex := by
  obtain ⟨s,t⟩ := b
  constructor
  · intro h
    change s.sum (fun _ n => n) + t.card = 0 at h
    have hs : s.sum (fun _ n => n) = 0 := by omega
    have ht : t.card = 0 := by omega
    have hs0 : s=0 := by
      ext i
      by_cases hi : i∈s.support
      · have hle : s i ≤ ∑ j∈s.support, s j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
        change s i ≤ s.sum (fun _ n => n) at hle
        simp only [hs, Nat.le_zero] at hle
        exact hle
      · exact Finsupp.notMem_support_iff.mp hi
    simp only [hs0, Finset.card_eq_zero.mp ht, scalarIndex]
  · intro h
    rw [h]
    simp [scalarIndex, totalLength]

/-- The scalar chain. -/
def unitChain : Chain := basis scalarIndex

@[simp] theorem unitChain_eq : unitChain = (1 : Poly) ⊗ₜ[ℂ] (1 : Exterior) := by
  simp [unitChain, scalarIndex, basis_apply, FiniteExterior.one_def]

/-- Augmentation is the scalar coefficient in the tensor-monomial basis. -/
def augmentation : Chain →ₗ[ℂ] ℂ := (Finsupp.lapply scalarIndex).comp basis.repr.toLinearMap

/-- Inclusion of scalar chains. -/
def inclusion : ℂ →ₗ[ℂ] Chain := LinearMap.toSpanSingleton ℂ Chain unitChain

@[simp] theorem augmentation_apply (u : Chain) : augmentation u = basis.repr u scalarIndex := rfl

@[simp] theorem augmentation_basis (b : BasisIndex) :
    augmentation (basis b) = if b=scalarIndex then 1 else 0 := by
  classical
  exact basis.repr_self_apply b scalarIndex

@[simp] theorem inclusion_apply (r : ℂ) : inclusion r = r • unitChain := rfl

@[simp] theorem d_unitChain : d unitChain = 0 := by
  change d (basis (0, ∅)) = 0
  simp only [d_basis, Finset.sum_empty]

@[simp] theorem H_unitChain : H unitChain = 0 := by
  change H (basis (0, ∅)) = 0
  simp only [H_basis, Finsupp.support_zero, Finset.sum_empty]

@[simp] theorem augmentation_unitChain : augmentation unitChain = 1 := by
  change augmentation (basis scalarIndex) = 1
  rw [augmentation_basis, if_pos rfl]

@[simp] theorem augmentation_inclusion (r : ℂ) : augmentation (inclusion r) = r := by
  rw [inclusion_apply, map_smul, augmentation_unitChain, smul_eq_mul, mul_one]

/-- The normalized Euler formula on each tensor-monomial basis vector. -/
theorem contraction_basis (b : BasisIndex) :
    d (homotopy (basis b)) + homotopy (d (basis b)) =
      basis b - inclusion (augmentation (basis b)) := by
  classical
  rw [homotopy_basis]
  change d ((totalLength b : ℂ)⁻¹ • H (basis b)) + H (inverseLength (d (basis b))) = _
  rw [inverseLength_d_basis, map_smul, map_smul, ← smul_add, euler_basis,
    smul_smul, augmentation_basis, inclusion_apply]
  by_cases hb : b=scalarIndex
  · subst b
    simp [totalLength, scalarIndex, unitChain]
  · have hn : totalLength b ≠ 0 := fun h => hb ((totalLength_zero_iff b).mp h)
    have hnc : (totalLength b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [if_neg hb, zero_smul, sub_zero, inv_mul_cancel₀ hnc, one_smul]

/-- An actual chain contraction identity, with a defined map and no exactness assumption. -/
theorem contraction : d.comp homotopy + homotopy.comp d =
    LinearMap.id - inclusion.comp augmentation := by
  apply basis.ext
  intro b
  exact contraction_basis b

theorem contraction_apply (u : Chain) :
    d (homotopy u) + homotopy (d u) = u - inclusion (augmentation u) :=
  LinearMap.congr_fun contraction u

@[simp] theorem d_inclusion (r : ℂ) : d (inclusion r) = 0 := by
  simp only [inclusion_apply, map_smul, d_unitChain, smul_zero]

/-- The scalar augmentation is a chain map for the actual differential. -/
@[simp] theorem augmentation_d (u : Chain) : augmentation (d u) = 0 := by
  have hcycle : d (homotopy (d u)) = d u := by
    have h := congrArg d (contraction_apply u)
    simpa only [map_add, d_square_zero, zero_add, map_sub, d_inclusion, sub_zero] using h
  have h := contraction_apply (d u)
  rw [d_square_zero, map_zero, add_zero, hcycle] at h
  have hi : inclusion (augmentation (d u)) = 0 := sub_eq_self.mp h.symm
  have ha := congrArg augmentation hi
  simpa only [augmentation_inclusion, map_zero] using ha
/-- Every augmented Koszul cycle has the displayed, explicitly defined preimage. -/
theorem preimage_of_augmented_cycle (u : Chain) (hd : d u = 0) (ha : augmentation u = 0) :
    d (homotopy u) = u := by
  simpa only [hd, ha, map_zero, add_zero, sub_zero] using contraction_apply u

theorem lengthOp_homotopy (u : Chain) : lengthOp (homotopy u) = homotopy (lengthOp u) := by
  have heq : lengthOp.comp homotopy = homotopy.comp lengthOp := by
    apply basis.ext
    intro b
    simp only [LinearMap.comp_apply, homotopy_basis, map_smul, lengthOp_H, lengthOp_basis]
    simp only [smul_smul, mul_comm]
  exact LinearMap.congr_fun heq u

end KhanSL2.BGG.PolynomialKoszul
