module

public import KhanSL2.SymmetricFamily.PolynomialPrimitiveNaturality
public import KhanSL2.Macdonald.RootFreeBidegree
public import KhanSL2.Macdonald.StrongBridgeHomologyCoproductFree
public import KhanSL2.Factorization.ShuffleNaturality

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Naturality of the genuine primitive coproduct under the actual free even
and odd embeddings, retaining the specified polynomial and exterior shuffle maps. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald
open SymmetricFamily BGGBridge

/-- The original color-zero inclusion of even polynomial variables. -/
def rootEvenPolynomialInclusion : RootEvenPolynomial →ₐ[ℂ] Poly :=
  MvPolynomial.rename (fun n : ℕ => (⟨n,0⟩ : Mode))

theorem rootEvenPolynomialInclusion_coproduct (p : RootEvenPolynomial) :
    symmetricCoproductAlg (rootEvenPolynomialInclusion p) =
      TensorProduct.map rootEvenPolynomialInclusion.toLinearMap
        rootEvenPolynomialInclusion.toLinearMap (polynomialPrimitive p) :=
  polynomialPrimitive_rename (fun n : ℕ => (⟨n,0⟩ : Mode)) p

/-- The actual color-zero odd inclusion respects the original signed exterior shuffle. -/
theorem rootOddExterior_coproduct (x : ExteriorAlgebra ℂ (Polynomial ℂ)) :
    exteriorCoproduct (rootOddExterior x) =
      TensorProduct.map rootOddExterior.toLinearMap rootOddExterior.toLinearMap
        (Factorization.ExteriorShuffle.shuffle (Polynomial ℂ) x) := by
  change TensorProduct.map exteriorEquiv.toLinearMap exteriorEquiv.toLinearMap
    (Factorization.ExteriorShuffle.shuffle KhanSL2.Current.plus
      (exteriorEquiv.symm (exteriorEquiv (ExteriorAlgebra.map rootOddCurrent x)))) = _
  rw [exteriorEquiv.symm_apply_apply,Factorization.ExteriorShuffle.shuffle_map]
  change ((TensorProduct.map exteriorEquiv.toLinearMap exteriorEquiv.toLinearMap).comp
    (TensorProduct.map (ExteriorAlgebra.map rootOddCurrent).toLinearMap
      (ExteriorAlgebra.map rootOddCurrent).toLinearMap))
        (Factorization.ExteriorShuffle.shuffle (Polynomial ℂ) x) = _
  rw [← TensorProduct.map_comp]
  rfl

/-- The original multiplication embedding has its literal even/odd tensor formula. -/
theorem strongFreeEmbedding_bidegree_tmul (q r : ℕ)
    (x : ⋀[ℂ]^q (Polynomial ℂ)) (p : RootEvenPower r) :
    strongFreeEmbedding (rootFreeBidegreeMap q r (x ⊗ₜ[ℂ] p)) =
      rootEvenPolynomialInclusion p.val ⊗ₜ[ℂ] rootOddExterior x.val := by
  change strongModel (rootEvenEmbedding p.val * rootOddStrongEmbedding x.val) = _
  rw [strongModel_mul,strongModel_rootEvenEmbedding]
  change (rootEvenPolynomialInclusion p.val ⊗ₜ[ℂ] (1 : Exterior)) *
    strongModel (StrongMacdonald.ofExt (rootOddExterior x.val)) = _
  rw [strongModel_ofExt,Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

/-- The existing homology comparison's free coproduct is the actual polynomial
primitive coproduct and original exterior shuffle, on each concrete bidegree. -/
theorem strongFreePrimitiveCoproduct_bidegree_tmul (q r : ℕ)
    (x : ⋀[ℂ]^q (Polynomial ℂ)) (p : RootEvenPower r) :
    TensorProduct.map strongFreeEmbedding strongFreeEmbedding
      (strongFreePrimitiveCoproduct (rootFreeBidegreeMap q r (x ⊗ₜ[ℂ] p))) =
      mixedCoproductReorder
        ((TensorProduct.map rootEvenPolynomialInclusion.toLinearMap
          rootEvenPolynomialInclusion.toLinearMap (polynomialPrimitive p.val)) ⊗ₜ[ℂ]
        (TensorProduct.map rootOddExterior.toLinearMap rootOddExterior.toLinearMap
          (Factorization.ExteriorShuffle.shuffle (Polynomial ℂ) x.val))) := by
  rw [strongFreePrimitiveCoproduct_embedding,strongFreeEmbedding_bidegree_tmul,
    mixedCoproduct_tmul,rootEvenPolynomialInclusion_coproduct,rootOddExterior_coproduct]

end KhanSL2.Macdonald
