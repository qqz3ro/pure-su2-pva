module

public import KhanSL2.Macdonald.RootEvenBlock
public import KhanSL2.SymmetricFamily.RootPolynomialBlock

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The normalized even block map is precisely literal restriction of its
symmetric root polynomial. Both sides retain the original normalizations. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.Macdonald
open SymmetricFamily

def rootEvenWordSection (k : ℕ) : RootEvenPower k →ₗ[ℂ] WordSpace ℕ k :=
  (relabel k).comp (rootEvenExponentEquiv k).toLinearMap

def rootEvenWordQuotient (k : ℕ) : WordSpace ℕ k →ₗ[ℂ] RootEvenPower k :=
  (rootEvenExponentEquiv k).symm.toLinearMap.comp (unlabel k)

@[simp] theorem rootEvenWordSection_quotient (k : ℕ) (x : WordSpace ℕ k) :
    rootEvenWordSection k (rootEvenWordQuotient k x) = wordAverage k x := by
  simp only [rootEvenWordSection,rootEvenWordQuotient,LinearMap.comp_apply,
    LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,relabel_unlabel]

theorem rootEvenWordSection_mem (k : ℕ) (p : RootEvenPower k) :
    rootEvenWordSection k p ∈ invariantWords k := relabel_mem k _

theorem rootEvenWordSection_tensor (k : ℕ) (p : RootEvenPower k) :
    rootEvenWordSection k p = (polynomialWordBasis k).repr (rootEvenToTensor k p) := by
  simp only [rootEvenWordSection,rootEvenToTensor,LinearMap.comp_apply,
    LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]

theorem rootEvenWordQuotient_val (k : ℕ) (x : WordSpace ℕ k) :
    (rootEvenWordQuotient k x).val = polynomialWordMap k x := by
  have ht := rootTensorToEven_coe k ((polynomialWordBasis k).repr.symm x)
  have hw := polynomialWordMap_rootEven k ((polynomialWordBasis k).repr.symm x)
  rw [LinearEquiv.apply_symm_apply] at hw
  have he : rootTensorToEven k ((polynomialWordBasis k).repr.symm x) = rootEvenWordQuotient k x := by
    simp only [rootTensorToEven,rootEvenWordQuotient,LinearMap.comp_apply,
      LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
  rw [he] at ht
  exact ht.trans hw.symm

/-- The original symmetric-root comparison followed by the actual polynomial inclusion. -/
def rootEvenRootMap (k : ℕ) : RootEvenPower k →ₗ[ℂ] MvPolynomial (Fin k) ℂ :=
  (MvPolynomial.symmetricSubalgebra (Fin k) ℂ).toSubmodule.subtype.comp
    (rootEvenPolynomialEquiv k).toLinearMap

theorem rootEvenRootMap_word (k : ℕ) (p : RootEvenPower k) :
    rootEvenRootMap k p = wordPolynomialEquiv k (rootEvenWordSection k p) := rfl

theorem rootEvenRootMap_quotient (k : ℕ) :
    (rootEvenRootMap k).comp (rootEvenWordQuotient k) =
      (wordPolynomialEquiv k).toLinearMap.comp (wordAverage k) := by
  apply LinearMap.ext
  intro x
  change rootEvenRootMap k (rootEvenWordQuotient k x) = _
  rw [rootEvenRootMap_word,rootEvenWordSection_quotient]
  rfl

/-- Literal ordered-block restriction between the original normalized even powers. -/
def rootEvenNormalizedBlock (r t : ℕ) : RootEvenPower (r+t) →ₗ[ℂ]
    RootEvenPower r ⊗[ℂ] RootEvenPower t :=
  (TensorProduct.map (rootEvenWordQuotient r) (rootEvenWordQuotient t)).comp
    ((wordBlock r t).comp (rootEvenWordSection (r+t)))

/-- The normalized homogeneous block has the previously specified actual polynomial value. -/
theorem rootEvenNormalizedBlock_val (r t : ℕ) (p : RootEvenPower (r+t)) :
    TensorProduct.map (RootEvenPower r).subtype (RootEvenPower t).subtype
      (rootEvenNormalizedBlock r t p) = rootEvenBlockPolynomial (firstBlock r t) p := by
  have hq (k : ℕ) : (RootEvenPower k).subtype.comp (rootEvenWordQuotient k) =
      polynomialWordMap k := LinearMap.ext (rootEvenWordQuotient_val k)
  change ((TensorProduct.map (RootEvenPower r).subtype (RootEvenPower t).subtype).comp
    (TensorProduct.map (rootEvenWordQuotient r) (rootEvenWordQuotient t)))
      (wordBlock r t (rootEvenWordSection (r+t) p)) = _
  rw [← TensorProduct.map_comp,hq,hq,← polynomialBlockWordMap_wordBlock,
    rootEvenWordSection_tensor]
  rfl

/-- Exact coefficient of the original primitive coproduct in the actual normalized block. -/
theorem rootEvenPrimitive_normalizedBlock (r t : ℕ) (p : RootEvenPower (r+t)) :
    polynomialPrimitiveComponent (r+t) r p.val =
      (Nat.choose (r+t) r : ℂ) •
        TensorProduct.map (RootEvenPower r).subtype (RootEvenPower t).subtype
          (rootEvenNormalizedBlock r t p) := by
  rw [rootEvenBlockPolynomial_normalization (firstBlock r t),rootEvenNormalizedBlock_val]

/-- The original normalized section becomes literal restriction of the actual root variables. -/
theorem rootEvenNormalizedBlock_roots (r t : ℕ) (p : RootEvenPower (r+t)) :
    TensorProduct.map (rootEvenRootMap r) (rootEvenRootMap t)
      (rootEvenNormalizedBlock r t p) = rootPolynomialBlock r t (rootEvenRootMap (r+t) p) := by
  change ((TensorProduct.map (rootEvenRootMap r) (rootEvenRootMap t)).comp
    (TensorProduct.map (rootEvenWordQuotient r) (rootEvenWordQuotient t)))
      (wordBlock r t (rootEvenWordSection (r+t) p)) = _
  rw [← TensorProduct.map_comp,rootEvenRootMap_quotient,rootEvenRootMap_quotient,
    TensorProduct.map_comp,LinearMap.comp_apply,
    wordBlock_average r t _ (rootEvenWordSection_mem (r+t) p),
    ← rootPolynomialBlock_word,rootEvenRootMap_word]

end KhanSL2.Macdonald
