module

public import KhanSL2.SymmetricFamily.ChartScalars
public import KhanSL2.SymmetricFamily.SymmetricChainFlat
public import KhanSL2.Factorization.CoefficientChainMaps
public import KhanSL2.Factorization.BalancedShuffleComplex

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

/-! The actual normalized symmetric coefficient chart map, followed by the
actual balanced relative CE shuffle. These maps are defined before any homology
identification, and their coefficient-unit formula retains the binomial factor. -/
noncomputable section
open scoped TensorProduct
open CategoryTheory
namespace KhanSL2.SymmetricFamily
open BGG BGGBridge Macdonald Factorization
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower
  coefficientChainSMulCommClass coefficientDegreeModule coefficientDegreeIsScalarTower
  coefficientDegreeSMulCommClass

variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB (r+s)) A]

/-- The independently specified actual total chain map over the chart algebra. -/
def symmetricChartTotalMap (c : Collision.ChartData (r+s) r s A) :
    RelativeChains (CoefficientBaseChange (Depth.RB (r+s)) (symmetricPower (r+s)) A) →ₗ[A]
      RelativeChains (FactorSymmetric r c.f₁) ⊗[A] RelativeChains (FactorSymmetric s c.f₂) :=
  (balancedRelativeShuffleLinear A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂)).comp
    (coefficientMapLinear A (symmetricChartCurrentMap c) (symmetricChartCurrentMap_smul c))

/-- The original coefficient coproduct specialized to the two actual factors,
followed by the actual balanced shuffle; normalization is kept separate. -/
def specializedSymmetricTotalMap (c : Collision.ChartData (r+s) r s A) :
    RelativeChains (symmetricPower (r+s)) →ₗ[ℂ]
      RelativeChains (FactorSymmetric r c.f₁) ⊗[A] RelativeChains (FactorSymmetric s c.f₂) :=
  (balancedRelativeShuffle A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂)).comp
    (Factorization.coefficientMap (specializedSymmetricCoproduct c).toLinearMap
      (constantEquivariant_of_lieHom (specializedSymmetricCoproduct c)))

/-- Exact normalization on every original relative chain, before homology. -/
theorem symmetricChartTotalMap_unit (c : Collision.ChartData (r+s) r s A)
    (z : RelativeChains (symmetricPower (r+s))) :
    symmetricChartTotalMap c (relativeChainsScalarMap (Depth.RB (r+s))
      (symmetricPower (r+s)) A ((1:A) ⊗ₜ[Depth.RB (r+s)] z)) =
        (Nat.choose (r+s) r : ℂ)⁻¹ • specializedSymmetricTotalMap c z := by
  have he : Factorization.coefficientMap (symmetricChartCurrentMap c).toLinearMap
      (constantEquivariant_of_lieHom (symmetricChartCurrentMap c))
      (relativeChainsScalarMap (Depth.RB (r+s)) (symmetricPower (r+s)) A
        ((1:A) ⊗ₜ[Depth.RB (r+s)] z)) =
      (Nat.choose (r+s) r : ℂ)⁻¹ • Factorization.coefficientMap (specializedSymmetricCoproduct c).toLinearMap
        (constantEquivariant_of_lieHom (specializedSymmetricCoproduct c)) z := by
    induction z using Submodule.Quotient.induction_on with
    | _ z =>
      change Factorization.coefficientMap _ _ (relativeChainsScalarMap _ _ _
        ((1:A) ⊗ₜ[Depth.RB (r+s)] (relC (symmetricPower (r+s))).mkQ z)) =
          _ • Factorization.coefficientMap _ _ ((relC (symmetricPower (r+s))).mkQ z)
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp only [map_add,TensorProduct.tmul_add,smul_add,hz,hw]
      | tmul ω p =>
        rw [relativeChainsScalarMap_tmul_mk]
        change (relC (BalancedCoefficients A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂))).mkQ
          (ω ⊗ₜ[ℂ] symmetricChartCurrentMap c
            (coefficientBaseChangeUnit (Depth.RB (r+s)) (symmetricPower (r+s)) A p)) =
          (Nat.choose (r+s) r : ℂ)⁻¹ •
            (relC (BalancedCoefficients A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂))).mkQ
              (ω ⊗ₜ[ℂ] specializedSymmetricCoproduct c p)
        rw [symmetricChartCurrentMap_unit,TensorProduct.tmul_smul,map_smul]
  change balancedRelativeShuffle A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂)
    (Factorization.coefficientMap (symmetricChartCurrentMap c).toLinearMap
      (constantEquivariant_of_lieHom (symmetricChartCurrentMap c))
      (relativeChainsScalarMap (Depth.RB (r+s)) (symmetricPower (r+s)) A
        ((1:A) ⊗ₜ[Depth.RB (r+s)] z))) = _
  rw [he,map_smul]
  rfl

theorem symmetricChartTotalMap_differential (c : Collision.ChartData (r+s) r s A)
    (z : RelativeChains (CoefficientBaseChange (Depth.RB (r+s)) (symmetricPower (r+s)) A)) :
    symmetricChartTotalMap c (differential _ z) =
      balancedTensorDifferential A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂)
        (symmetricChartTotalMap c z) := by
  change balancedRelativeShuffle A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂)
    (Factorization.coefficientMap (symmetricChartCurrentMap c).toLinearMap
      (constantEquivariant_of_lieHom (symmetricChartCurrentMap c)) (differential _ z)) = _
  rw [coefficientMap_differential,balancedRelativeShuffle_differential]
  rfl

/-- The same original map restricted to the actual exterior-degree chain groups. -/
def symmetricChartComplex (c : Collision.ChartData (r+s) r s A) :
    coefficientRelativeComplex A
      (CoefficientBaseChange (Depth.RB (r+s)) (symmetricPower (r+s)) A) ⟶
      balancedTensorComplex A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂) :=
  coefficientRelativeComplexMap A (symmetricChartCurrentMap c) (symmetricChartCurrentMap_smul c) ≫
    balancedShuffleComplex A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂)

theorem symmetricChartComplex_forget (c : Collision.ChartData (r+s) r s A) (j : ℕ)
    (z : degree (CoefficientBaseChange (Depth.RB (r+s)) (symmetricPower (r+s)) A) j) :
    balancedTensorDegreeForget A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂) j
      ((symmetricChartComplex c).f j z) = symmetricChartTotalMap c z.val := by
  exact balancedTensorDegreeForget_degreeShuffle A (FactorSymmetric r c.f₁)
    (FactorSymmetric s c.f₂) j
      (coefficientDegreeMapLinear A (symmetricChartCurrentMap c) (symmetricChartCurrentMap_smul c) j z)

/-- Once the actual chart map is a quasi-isomorphism, every scalar specialization
is valid by its nonnegative flat-term cone, without commuting homology and fibres. -/
theorem symmetricChartComplex_specialization (c : Collision.ChartData (r+s) r s A)
    [QuasiIso (symmetricChartComplex c)] (S : Type) [CommRing S] [Algebra A S] :
    QuasiIso (NonnegativeCone.scalarMap S (symmetricChartComplex c)) := by
  let : ∀ j, Module.Flat A ((coefficientRelativeComplex A
    (CoefficientBaseChange (Depth.RB (r+s)) (symmetricPower (r+s)) A)).X j) :=
      symmetricBaseChangedComplex_flat (r+s) A
  let : ∀ j, Module.Flat A
      ((balancedTensorComplex A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂)).X j) :=
    fun j => factorSymmetricTensorComplex_flat r s j c.f₁ c.f₂
  exact NonnegativeCone.quasiIso_scalarMap_of_flat (symmetricChartComplex c) S

end KhanSL2.SymmetricFamily
