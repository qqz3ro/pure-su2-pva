module

public import KhanSL2.Injectivity.ClosedCurrentFamilies
public import KhanSL2.Injectivity.RootEncodingSupport
public import KhanSL2.Injectivity.RootCycles

/-! Explicit Newton cycles as actual finite Cartan chains, with functionals
on the original relative cohomology quotient. -/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace KhanSL2.Injectivity.Cartan

abbrev RootPolynomial (s : ℕ) := MvPolynomial (Fin s ⊕ Fin s) ℂ

def rootFamily (s : ℕ) : ClosedCurrentFamily (RootPolynomial s) (rootCurrentPolynomial s) where
  toLinearMap := rootEncode s
  closed := rootEncode_pairing_q
  current := rootCurrentAction_rootEncode

def rootTheta (s n : ℕ) : ℕ →₀ RootPolynomial s :=
  rootCycle (fun i : Fin s => MvPolynomial.X (.inl i))
    (fun i : Fin s => MvPolynomial.X (.inr i)) (s + 1 + n)

@[simp] theorem rootTheta_zero (s n : ℕ) : rootTheta s n 0 = 0 :=
  rootCycle_apply_zero _ _ _

theorem rootTheta_cycle (s n : ℕ) :
    ∑ j ∈ (rootTheta s n).support, rootCurrentPolynomial s j * rootTheta s n j = 0 := by
  simp only [rootCurrentPolynomial_eq_powerSum, rootTheta]
  apply rootCycle_current_sum_eq_zero
  simp only [Fintype.card_fin]
  omega

/-- Successive explicit finite Newton insertions. Each stage is proved closed
for the actual Cartan CE differential and equivariant for every current. -/
def newtonFamily (s : ℕ) : List ℕ → ClosedCurrentFamily (RootPolynomial s) (rootCurrentPolynomial s)
  | [] => rootFamily s
  | n :: ns => (newtonFamily s ns).insert (rootTheta s n)
      (rootTheta_zero s n) (rootTheta_cycle s n)

@[simp] theorem newtonFamily_nil (s : ℕ) : newtonFamily s [] = rootFamily s := rfl

@[simp] theorem newtonFamily_cons (s n : ℕ) (ns : List ℕ) (p : RootPolynomial s) :
    (newtonFamily s (n :: ns)).toLinearMap p =
      ∑ j ∈ (rootTheta s n).support, generator (.cartan (j - 1)) *
        (newtonFamily s ns).toLinearMap (rootTheta s n j * p) := rfl

/-- The finite chain used for a list of neutral indices and Newton cycles. -/
def separatingFamily (s : ℕ) (ns : List ℕ) :
    List ℕ → ClosedCurrentFamily (RootPolynomial s) (rootCurrentPolynomial s)
  | [] => newtonFamily s ns
  | i :: is => (separatingFamily s ns is).prependNeutral i

def separatingFunctional (s : ℕ) (ns is : List ℕ) (p : RootPolynomial s) :
    KhanSL2.Cohomology →ₗ[ℂ] ℂ :=
  (separatingFamily s ns is).functional p

@[simp] theorem separatingFunctional_classOf (s : ℕ) (ns is : List ℕ) (p : RootPolynomial s)
    (u : KhanSL2.Cochain) (hu : u ∈ relativeCycles) :
    separatingFunctional s ns is p (classOf u hu) =
      FiniteExterior.coefficientPairing ((separatingFamily s ns is).toLinearMap p)
        (restriction u) := rfl

/-- The constructed chains annihilate every CE coboundary before taking invariants. -/
theorem separatingFamily_pairing_q (s : ℕ) (ns is : List ℕ) (p : RootPolynomial s)
    (u : Cochain) :
    FiniteExterior.coefficientPairing ((separatingFamily s ns is).toLinearMap p) (q u) = 0 :=
  (separatingFamily s ns is).closed p u

theorem separatingFunctional_phi_X (s : ℕ) (ns is : List ℕ) (p : RootPolynomial s) (n : ℕ) :
    separatingFunctional s ns is p (phi (Source.X n)) =
      FiniteExterior.coefficientPairing ((separatingFamily s ns is).toLinearMap p)
        ((translation ^ n) (generator (.neutral 0) * generator (.cartan 0))) :=
  descendCartanFunctional_phi_X _ ((separatingFamily s ns is).closed p) n

theorem separatingFunctional_phi_Y (s : ℕ) (ns is : List ℕ) (p : RootPolynomial s) (n : ℕ) :
    separatingFunctional s ns is p (phi (Source.Y n)) =
      (-2 : ℂ) * FiniteExterior.coefficientPairing ((separatingFamily s ns is).toLinearMap p)
        ((translation ^ n)
          ((generator (.neutral 0) * generator (.plus 0)) * generator (.minus 0))) :=
  descendCartanFunctional_phi_Y _ ((separatingFamily s ns is).closed p) n

end KhanSL2.Injectivity.Cartan
