module

public import KhanSL2.SymmetricFamily.SymmetricBlockCoproduct
public import KhanSL2.Macdonald.RootEvenShift

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Exact primitive-versus-normalized-block comparison for the original
uncolored even Macdonald generators. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.Macdonald
open SymmetricFamily

/-- Labelled-word multiplication is the original multiplication of even variables. -/
theorem polynomialWordMap_rootEven (k : ℕ) (z : ⨂[ℂ]^k (Polynomial ℂ)) :
    polynomialWordMap k ((polynomialWordBasis k).repr z) = rootEvenTensorProduct k z := by
  have h : (polynomialWordMap k).comp (polynomialWordBasis k).repr.toLinearMap =
      rootEvenTensorProduct k := by
    apply (polynomialWordBasis k).ext
    intro u
    change polynomialWordMap k ((polynomialWordBasis k).repr (polynomialWordBasis k u)) =
      rootEvenTensorProduct k (polynomialWordBasis k u)
    rw [Module.Basis.repr_self,polynomialWordMap_single,one_smul,
      polynomialWordBasis_apply,rootEvenTensorProduct_tprod]
    simp only [rootEvenVariable_X_pow,subsetPolynomial]
  exact LinearMap.congr_fun h z

/-- The actual normalized even section in labelled-word coordinates is invariant. -/
theorem rootEvenToTensor_repr_invariant (k : ℕ) (p : RootEvenPower k) :
    (polynomialWordBasis k).repr (rootEvenToTensor k p) ∈ invariantWords k := by
  intro σ
  rw [← polynomialWordBasis_repr_permute,rootEvenToTensor_invariant]

/-- Multiply the chosen two blocks of the original normalized even tensor section. -/
def rootEvenBlockPolynomial {k r : ℕ} (S : Assignment k r) :
    RootEvenPower k →ₗ[ℂ] RootEvenPolynomial ⊗[ℂ] RootEvenPolynomial :=
  (polynomialBlockWordMap S).comp
    ((polynomialWordBasis k).repr.toLinearMap.comp (rootEvenToTensor k))

/-- The genuine primitive even coproduct component has exactly the binomial
factor relative to literal splitting of normalized labelled root tensors. -/
theorem rootEvenBlockPolynomial_normalization {k r : ℕ}
    (S : Assignment k r) (p : RootEvenPower k) :
    polynomialPrimitiveComponent k r p.val =
      (Nat.choose k r : ℂ) • rootEvenBlockPolynomial S p := by
  have h := polynomialPrimitiveComponent_normalized S
    ((polynomialWordBasis k).repr (rootEvenToTensor k p))
  rw [polynomialWordMap_rootEven,← rootTensorToEven_coe,
    rootTensorToEven_rootEvenToTensor] at h
  rw [wordAverage_eq_self (rootEvenToTensor_repr_invariant k p)] at h
  exact h

end KhanSL2.Macdonald
