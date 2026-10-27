module

public import KhanSL2.Injectivity.RootPolynomialEncoding
public import KhanSL2.Injectivity.CartanSupport

@[expose] public section

noncomputable section

namespace KhanSL2.Injectivity.Cartan

theorem orderedProduct_mem_rootOnly {n : ℕ} (f : Fin n → Cochain)
    (hf : ∀ i, f i ∈ rootOnly) : orderedProduct f ∈ rootOnly := by
  induction n with
  | zero => simpa using rootOnly_one
  | succ n ih =>
    rw [orderedProduct_succ]
    exact rootOnly_mul (hf 0) (ih (Fin.tail f) (fun i => hf i.succ))

theorem rootWord_mem_rootOnly {s : ℕ} (a b : Fin s → ℕ) : rootWord a b ∈ rootOnly :=
  rootOnly_mul (orderedProduct_mem_rootOnly _ (fun i => rootOnly_plus (a i)))
    (orderedProduct_mem_rootOnly _ (fun i => rootOnly_minus (b i)))

theorem rootMonomial_mem_rootOnly {s : ℕ} (d : (Fin s ⊕ Fin s) →₀ ℕ) :
    rootMonomial d ∈ rootOnly := rootWord_mem_rootOnly _ _

/-- Encoded polynomials have no Cartan factors. -/
theorem rootEncode_mem_rootOnly {s : ℕ} (P : MvPolynomial (Fin s ⊕ Fin s) ℂ) :
    rootEncode s P ∈ rootOnly := by
  refine MvPolynomial.induction_on' P ?_ ?_
  · intro d c
    rw [rootEncode_monomial]
    exact rootOnly.smul_mem c (rootMonomial_mem_rootOnly d)
  · intro P Q hP hQ
    rw [map_add]
    exact rootOnly.add_mem hP hQ

/-- The base of the Cartan-chain induction annihilates the full CE differential. -/
theorem rootEncode_pairing_q {s : ℕ} (P : MvPolynomial (Fin s ⊕ Fin s) ℂ) (u : Cochain) :
    FiniteExterior.coefficientPairing (rootEncode s P) (q u) = 0 :=
  rootOnly_pairing_q (rootEncode_mem_rootOnly P) u

end KhanSL2.Injectivity.Cartan
