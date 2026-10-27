module

public import KhanSL2.Macdonald.CurrentActionDegree

@[expose] public section

/-! Canonical homogeneous projections are current-module morphisms and commute
with raising coefficient operators. No graded decomposition is assumed. -/

noncomputable section
namespace KhanSL2.Macdonald

/-- A degree-preserving linear operator commutes with the actual homogeneous projections. -/
theorem homogeneousComponent_comm_of_preserves_degree (F : Module.End ℂ Poly)
    (hF : ∀ (k : ℕ) (p : Poly), p ∈ MvPolynomial.homogeneousSubmodule Mode ℂ k →
      F p ∈ MvPolynomial.homogeneousSubmodule Mode ℂ k) (k : ℕ) (p : Poly) :
    MvPolynomial.homogeneousComponent k (F p) = F (MvPolynomial.homogeneousComponent k p) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial d c =>
    have h := MvPolynomial.isHomogeneous_monomial c (rfl : d.degree = d.degree)
    rw [MvPolynomial.homogeneousComponent_of_mem (hF d.degree _ h),
      MvPolynomial.homogeneousComponent_of_mem h]
    split_ifs <;> simp

/-- The projection commutes with every linearly extended current-space endomorphism. -/
theorem homogeneousComponent_symmetricDerivation (D : Module.End ℂ BGG.Current)
    (k : ℕ) (p : Poly) :
    MvPolynomial.homogeneousComponent k (symmetricDerivation D p) =
      symmetricDerivation D (MvPolynomial.homogeneousComponent k p) :=
  homogeneousComponent_comm_of_preserves_degree (symmetricDerivation D).toLinearMap
    (fun _ _ hp => symmetricDerivation_preserves_degree D hp) k p

/-- Project symmetric current coefficients to their actual homogeneous degree-k part. -/
def symmetricPowerProjection (k : ℕ) :
    SymmetricCoefficients →ₗ⁅ℂ,BGG.Current⁆ symmetricPower k where
  toFun p := ⟨MvPolynomial.homogeneousComponent k p, MvPolynomial.homogeneousComponent_mem k p⟩
  map_add' p q := by
    apply Subtype.ext
    exact map_add (MvPolynomial.homogeneousComponent k) (show Poly from p) (show Poly from q)
  map_smul' c p := by
    apply Subtype.ext
    exact map_smul (MvPolynomial.homogeneousComponent k) c (show Poly from p)
  map_lie' {x p} := by
    apply Subtype.ext
    exact homogeneousComponent_symmetricDerivation (LieAlgebra.ad ℂ BGG.Current x) k p

@[simp] theorem symmetricPowerProjection_apply (k : ℕ) (p : SymmetricCoefficients) :
    (symmetricPowerProjection k p : SymmetricCoefficients) =
      MvPolynomial.homogeneousComponent k p := rfl

@[simp] theorem symmetricPowerProjection_incl (k : ℕ) (p : symmetricPower k) :
    symmetricPowerProjection k ((symmetricPower k).incl p) = p := by
  apply Subtype.ext
  exact MvPolynomial.homogeneousComponent_eq_self p.property

theorem symmetricPowerProjection_coefficientEnd (m k : ℕ) (p : SymmetricCoefficients) :
    symmetricPowerProjection k (symmetricCoefficientEnd m p) =
      symmetricPowerCoefficientEnd m k (symmetricPowerProjection k p) := by
  apply Subtype.ext
  exact homogeneousComponent_symmetricDerivation (Modules.coefficientShift m) k p

end KhanSL2.Macdonald
