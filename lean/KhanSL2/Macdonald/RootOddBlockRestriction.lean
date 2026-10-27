module

public import KhanSL2.SymmetricFamily.SignedWordBlock
public import KhanSL2.SymmetricFamily.RootPolynomialBlock
public import KhanSL2.SymmetricFamily.UncoloredExterior
public import KhanSL2.Factorization.ExteriorBlockTensor

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Literal block restriction of the original normalized odd root model,
retaining its antisymmetrization and the original exterior-power quotient. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald
open SymmetricFamily PolynomialBGG

def rootOddWordSection (q : ℕ) : (⋀[ℂ]^q (Polynomial ℂ)) →ₗ[ℂ] WordSpace ℕ q :=
  (polynomialWordBasis q).repr.toLinearMap.comp (exteriorToTensor (Polynomial ℂ) q)

def rootOddWordQuotient (q : ℕ) : WordSpace ℕ q →ₗ[ℂ] (⋀[ℂ]^q (Polynomial ℂ)) :=
  (tensorToExterior (Polynomial ℂ) q).comp (polynomialWordBasis q).repr.symm.toLinearMap

@[simp] theorem rootOddWordQuotient_single (q : ℕ) (u : Fin q → ℕ) (c : ℂ) :
    rootOddWordQuotient q (Finsupp.single u c) =
      c • exteriorPower.ιMulti ℂ q (fun i => (Polynomial.X : Polynomial ℂ)^u i) := by
  simp only [rootOddWordQuotient,LinearMap.comp_apply,LinearEquiv.coe_coe,
    Module.Basis.repr_symm_single,map_smul,polynomialWordBasis_apply,tensorToExterior_tprod]

@[simp] theorem rootOddWordSection_quotient (q : ℕ) (x : WordSpace ℕ q) :
    rootOddWordSection q (rootOddWordQuotient q x) = signedWordAverage q x := by
  change (polynomialWordBasis q).repr
    (((exteriorToTensor (Polynomial ℂ) q).comp (tensorToExterior (Polynomial ℂ) q))
      ((polynomialWordBasis q).repr.symm x)) = _
  rw [alternatingProjection_eq_signedAverage,polynomialWordBasis_repr_signedAverage,
    LinearEquiv.apply_symm_apply]

theorem rootOddWordSection_fixed (q : ℕ) (x : ⋀[ℂ]^q (Polynomial ℂ))
    (σ : Equiv.Perm (Fin q)) : signedWordPermute σ (rootOddWordSection q x) = rootOddWordSection q x := by
  change signedWordPermute σ ((polynomialWordBasis q).repr (exteriorToTensor (Polynomial ℂ) q x)) = _
  rw [← polynomialWordBasis_repr_signedSlot,
    exteriorToTensor_mem_signed (Polynomial ℂ) q x σ]
  rfl

/-- The original alternating root equivalence followed by its actual polynomial inclusion. -/
def rootOddRootMap (q : ℕ) : (⋀[ℂ]^q (Polynomial ℂ)) →ₗ[ℂ] MvPolynomial (Fin q) ℂ :=
  (alternatingRootPolynomials q).subtype.comp (exteriorPolynomialEquiv q).toLinearMap

theorem rootOddRootMap_word (q : ℕ) (x : ⋀[ℂ]^q (Polynomial ℂ)) :
    rootOddRootMap q x = wordPolynomialEquiv q (rootOddWordSection q x) := rfl

theorem rootOddRootMap_quotient (q : ℕ) :
    (rootOddRootMap q).comp (rootOddWordQuotient q) =
      (wordPolynomialEquiv q).toLinearMap.comp (signedWordAverage q) := by
  apply LinearMap.ext
  intro x
  change rootOddRootMap q (rootOddWordQuotient q x) = _
  rw [rootOddRootMap_word,rootOddWordSection_quotient]
  rfl

/-- Apply the original exterior quotients to the two literal ordered blocks. -/
def rootOddNormalizedBlock (r t : ℕ) : (⋀[ℂ]^(r+t) (Polynomial ℂ)) →ₗ[ℂ]
    (⋀[ℂ]^r (Polynomial ℂ)) ⊗[ℂ] (⋀[ℂ]^t (Polynomial ℂ)) :=
  (TensorProduct.map (rootOddWordQuotient r) (rootOddWordQuotient t)).comp
    ((wordBlock r t).comp (rootOddWordSection (r+t)))

/-- In ambient exterior coordinates this is the original two-block wedge map. -/
theorem rootOddNormalizedBlock_val (r t : ℕ) (x : ⋀[ℂ]^(r+t) (Polynomial ℂ)) :
    TensorProduct.map (ExteriorAlgebra.exteriorPower ℂ r (Polynomial ℂ)).subtype
      (ExteriorAlgebra.exteriorPower ℂ t (Polynomial ℂ)).subtype
        (rootOddNormalizedBlock r t x) =
      Factorization.ExteriorBlock.tensorBlockMap (Polynomial ℂ) r t
        (exteriorToTensor (Polynomial ℂ) (r+t) x) := by
  have h : (TensorProduct.map (ExteriorAlgebra.exteriorPower ℂ r (Polynomial ℂ)).subtype
      (ExteriorAlgebra.exteriorPower ℂ t (Polynomial ℂ)).subtype).comp
      ((TensorProduct.map (rootOddWordQuotient r) (rootOddWordQuotient t)).comp (wordBlock r t)) =
      (Factorization.ExteriorBlock.tensorBlockMap (Polynomial ℂ) r t).comp
        (polynomialWordBasis (r+t)).repr.symm.toLinearMap := by
    apply Finsupp.lhom_ext
    intro u c
    simp only [LinearMap.comp_apply,wordBlock_single,map_smul,TensorProduct.map_tmul,
      rootOddWordQuotient_single,one_smul,Submodule.subtype_apply,LinearEquiv.coe_coe,
      Module.Basis.repr_symm_single,polynomialWordBasis_apply,
      Factorization.ExteriorBlock.tensorBlockMap_tprod]
    rfl
  have hx := LinearMap.congr_fun h (rootOddWordSection (r+t) x)
  change _ = Factorization.ExteriorBlock.tensorBlockMap (Polynomial ℂ) r t
    ((polynomialWordBasis (r+t)).repr.symm
      ((polynomialWordBasis (r+t)).repr (exteriorToTensor (Polynomial ℂ) (r+t) x))) at hx
  rw [LinearEquiv.symm_apply_apply] at hx
  exact hx

/-- The actual original normalized odd tensor has the inverse-binomial exterior block value. -/
theorem rootOddNormalizedBlock_exteriorBlock (r t : ℕ) (x : ⋀[ℂ]^(r+t) (Polynomial ℂ)) :
    TensorProduct.map (ExteriorAlgebra.exteriorPower ℂ r (Polynomial ℂ)).subtype
      (ExteriorAlgebra.exteriorPower ℂ t (Polynomial ℂ)).subtype (rootOddNormalizedBlock r t x) =
        (Nat.choose (r+t) r : ℂ)⁻¹ • Factorization.ExteriorBlock.exteriorBlockMap (Polynomial ℂ) r t x := by
  rw [rootOddNormalizedBlock_val,Factorization.ExteriorBlock.tensorBlockMap_exteriorToTensor]

/-- Signed normalized block restriction is literal restriction of the alternating root polynomial. -/
theorem rootOddNormalizedBlock_roots (r t : ℕ) (x : ⋀[ℂ]^(r+t) (Polynomial ℂ)) :
    TensorProduct.map (rootOddRootMap r) (rootOddRootMap t) (rootOddNormalizedBlock r t x) =
      rootPolynomialBlock r t (rootOddRootMap (r+t) x) := by
  change ((TensorProduct.map (rootOddRootMap r) (rootOddRootMap t)).comp
    (TensorProduct.map (rootOddWordQuotient r) (rootOddWordQuotient t)))
      (wordBlock r t (rootOddWordSection (r+t) x)) = _
  rw [← TensorProduct.map_comp,rootOddRootMap_quotient,rootOddRootMap_quotient,
    TensorProduct.map_comp,LinearMap.comp_apply,
    wordBlock_signedAverage r t _ (rootOddWordSection_fixed (r+t) x),
    ← rootPolynomialBlock_word,rootOddRootMap_word]

end KhanSL2.Macdonald
