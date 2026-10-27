module

public import KhanSL2.SymmetricFamily.RootPermutation

@[expose] public section

/-! Factor coefficient ideals characterize genuine polynomial identities after
any algebra homomorphism, rather than only identities on reduced points. -/

noncomputable section
open Polynomial
namespace KhanSL2.SymmetricFamily
open Factorization.WeightedRoots

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Vanishing of the coefficient ideal is the full polynomial identity. -/
theorem coefficientIdeal_le_ker_iff (f : R →+* S) (p : R[X]) :
    coefficientIdeal p ≤ RingHom.ker f ↔ p.map f = 0 := by
  rw [coefficientIdeal, Ideal.span_le]
  constructor
  · intro h
    apply Polynomial.ext
    intro n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact h ⟨n,rfl⟩
  · intro h a ha
    obtain ⟨n,rfl⟩ := ha
    have hn := congrArg (fun q : S[X] => q.coeff n) h
    change f (p.coeff n) = 0
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using hn

/-- The actual two factor ideals are exactly the equations they were defined to impose. -/
theorem factorIdeal_le_ker_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : R →+* S) (f₁ f₂ : R[X]) (x : ι → R) (m : ι → ℕ) (T : Finset ι) :
    factorIdeal f₁ f₂ x m T ≤ RingHom.ker f ↔
      rootProduct (fun i => f (x i)) m T = f₁.map f ∧
      rootProduct (fun i => f (x i)) m Tᶜ = f₂.map f := by
  simp only [factorIdeal, sup_le_iff, coefficientIdeal_le_ker_iff,
    Polynomial.map_sub, rootProduct_map, sub_eq_zero]

end KhanSL2.SymmetricFamily
