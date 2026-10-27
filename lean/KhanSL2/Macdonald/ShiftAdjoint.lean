module

public import KhanSL2.Macdonald.CurrentActionShift
public import KhanSL2.Macdonald.CoefficientShift
public import KhanSL2.Macdonald.DerivationFiniteSum
public import KhanSL2.Macdonald.TensorPairing

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The previously constructed lowering operators really are the restricted
duals of the actual raising coefficient power sums. -/
noncomputable section
open scoped BigOperators TensorProduct
namespace KhanSL2.Macdonald

private def raiseMode (m : ℕ) (i : Mode) : Mode := ⟨m+i.index,i.color⟩
private def lowerMode (m : ℕ) (i : Mode) : Mode := ⟨i.index-m,i.color⟩

private theorem raiseMode_eq_iff (m : ℕ) (i j : Mode) (hj : m ≤ j.index) :
    raiseMode m i = j ↔ i = lowerMode m j := by
  constructor
  · intro h
    apply BGG.PositiveCE.Mode.ext
    · have hh := congrArg BGG.PositiveCE.Mode.index h
      change m+i.index = j.index at hh
      change i.index = j.index-m
      omega
    · simpa only [raiseMode, lowerMode] using congrArg BGG.PositiveCE.Mode.color h
  · intro h
    subst i
    apply BGG.PositiveCE.Mode.ext
    · change m + (j.index-m) = j.index
      omega
    · rfl

private def finiteLowering (m : ℕ) (S : Finset Mode) : Derivation ℂ Poly Poly :=
  ∑ i ∈ S, (MvPolynomial.X i : Poly) • MvPolynomial.pderiv (raiseMode m i)

private theorem finiteLowering_apply (m : ℕ) (S : Finset Mode) (p : Poly) :
    finiteLowering m S p =
      ∑ i ∈ S, MvPolynomial.X i * MvPolynomial.pderiv (raiseMode m i) p := by
  simp [finiteLowering, smul_eq_mul]

private theorem finiteLowering_X (m : ℕ) (S : Finset Mode) (j : Mode)
    (hS : m ≤ j.index → lowerMode m j ∈ S) :
    finiteLowering m S (MvPolynomial.X j) = polynomialShift m (MvPolynomial.X j) := by
  classical
  rw [finiteLowering_apply]
  have hX : polynomialShift m (MvPolynomial.X j) =
      if m ≤ j.index then MvPolynomial.X (lowerMode m j) else 0 := by
    cases j
    exact polynomialShift_X _ _ _
  rw [hX]
  by_cases hj : m ≤ j.index
  · simp only [MvPolynomial.pderiv_X, Pi.single_apply, if_pos hj]
    have hc (i : Mode) : j = raiseMode m i ↔ lowerMode m j = i := by
      simpa only [eq_comm] using raiseMode_eq_iff m i j hj
    simp only [hc]
    simp [hS hj]
  · have hc (i : Mode) : j ≠ raiseMode m i := by
      intro hh
      have h := hh.symm
      have hh := congrArg BGG.PositiveCE.Mode.index h
      change m+i.index = j.index at hh
      omega
    simp [MvPolynomial.pderiv_X, Pi.single_apply, hc, Ne.symm, hj]

/-- The polynomial lowering derivation is transpose to the raising derivation
on the genuine symmetric current module, with the factorial normalization. -/
theorem polynomialShift_pairing (m : ℕ) (p q : Poly) :
    polynomialPairing (symmetricCoefficientShift m p) q =
      polynomialPairing p (polynomialShift m q) := by
  classical
  let S := p.vars ∪ q.vars.image (lowerMode m)
  have hp : p.vars ⊆ S := Finset.subset_union_left
  have hl : polynomialShift m q = finiteLowering m S q := by
    apply MvPolynomial.derivation_eq_of_forall_mem_vars
    intro j hj
    apply (finiteLowering_X m S j _).symm
    intro _
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,hj,rfl⟩)
  rw [polynomialDerivation_apply_finite (symmetricCoefficientShift m) S p hp,
    hl, finiteLowering_apply]
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hXi : symmetricCoefficientShift m (MvPolynomial.X i) = MvPolynomial.X (raiseMode m i) := by
    cases i
    exact symmetricCoefficientShift_X _ _ _
  rw [hXi, polynomialPairing_vectorField]

/-- Actual raising action on the chain coordinates. -/
def chainCoefficientShift (m : ℕ) : Module.End ℂ W :=
  TensorProduct.map (symmetricCoefficientShift m).toLinearMap LinearMap.id

/-- The full mixed pairing identifies the previously explicit coefficient
lowering operator with the transpose of the true symmetric coefficient action. -/
theorem coefficientShift_pairing (m : ℕ) (u v : W) :
    pairing (chainCoefficientShift m u) v = pairing u (coefficientShift m v) :=
  pairing_tensor_map _ _ LinearMap.id LinearMap.id
    (polynomialShift_pairing m) (fun _ _ => rfl) u v

end KhanSL2.Macdonald
