module

public import KhanSL2.SymmetricFamily.RootTensorWords
public import KhanSL2.SymmetricFamily.CurrentTensorSection

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-! Literal block restriction of arbitrary actual current tensors agrees with
the actual coefficient-chart quotient in root coordinates. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Macdonald
open scoped FactorRootScalars

variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB (r+s)) A]

/-- The original root quotient, restricted to one distinguished actual assignment. -/
def chartTensorRootRestriction (c : Collision.ChartData (r+s) r s A) :
    (⨂[ℂ]^(r+s) BGG.Current) →ₗ[ℂ] FactorColors r c.f₁ ⊗[A] FactorColors s c.f₂ :=
  ((coloredBlockTensorEquiv c).toLinearMap.restrictScalars ℂ).comp
    ((((LinearMap.proj (firstBlock r s)).comp
      (coloredAssignmentSplitting (r+s) A c).toLinearMap).restrictScalars ℂ).comp
      (((baseRootTensorEquiv (r+s) A).toLinearMap.restrictScalars ℂ).comp
        ((TensorProduct.mk (Depth.RB (r+s)) A (⨂[ℂ]^(r+s) BGG.Current) 1).restrictScalars ℂ)))

/-- No averaging or altered coefficient map enters the raw root-block comparison. -/
theorem chartTensorRootRestriction_eq (c : Collision.ChartData (r+s) r s A) :
    chartTensorRootRestriction c =
      (tensorOverMap (A:=A) (factorTensorUnit r c.f₁) (factorTensorUnit s c.f₂)).comp
        (tensorSlotsBlockEquiv BGG.Current r s).toLinearMap := by
  apply (tensorCurrentBasis (r+s)).ext
  intro q
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,tensorCurrentBasis_apply,
    tensorSlotsBlockEquiv_tprod,tensorOverMap_tmul]
  exact coloredBlockTensorEquiv_word c (fun i => (q i).1) (fun i => (q i).2)

omit [IsScalarTower ℂ (Depth.RB (r+s)) A] in
/-- Faithful factor coordinates intertwine canonical specialization with the
original normalized sections on each tensor factor. -/
theorem factorSymmetricTensorInclusion_specialize (c : Collision.ChartData (r+s) r s A)
    (z : symmetricPower r ⊗[ℂ] symmetricPower s) :
    factorSymmetricTensorInclusion c
      (tensorOverMap (A:=A) (factorSymmetricUnit r c.f₁) (factorSymmetricUnit s c.f₂) z) =
      tensorOverMap (A:=A) (factorTensorUnit r c.f₁) (factorTensorUnit s c.f₂)
        (TensorProduct.map (symmetricToTensor r) (symmetricToTensor s) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y =>
    rw [tensorOverMap_tmul,factorSymmetricTensorInclusion_tmul,
      factorSymmetricFixedEquiv_unit,factorSymmetricFixedEquiv_unit,
      TensorProduct.map_tmul,tensorOverMap_tmul]

/-- The original normalized tensor block specializes to the actual chart equivalence. -/
theorem symmetricTensorBlock_chart (c : Collision.ChartData (r+s) r s A)
    (p : symmetricPower (r+s)) :
    tensorOverMap (A:=A) (factorSymmetricUnit r c.f₁) (factorSymmetricUnit s c.f₂)
      (symmetricTensorBlock r s p) =
        symmetricChartEquiv c (show CoefficientBaseChange (Depth.RB (r+s)) (symmetricPower (r+s)) A
          from 1 ⊗ₜ[Depth.RB (r+s)] p) := by
  apply factorSymmetricTensorInclusion_injective c
  rw [factorSymmetricTensorInclusion_specialize,symmetricTensorBlock_section,
    factorSymmetricTensorInclusion_chart]
  exact (LinearMap.congr_fun (chartTensorRootRestriction_eq c) (symmetricToTensor (r+s) p)).symm

/-- The original primitive coproduct specializes to precisely the binomial
multiple of the actual normalized chart equivalence. -/
theorem symmetricCoproductComponent_chart (c : Collision.ChartData (r+s) r s A)
    (p : symmetricPower (r+s)) :
    tensorOverMap (A:=A) (factorSymmetricUnit r c.f₁) (factorSymmetricUnit s c.f₂)
      (symmetricCoproductComponent r s p) =
        (Nat.choose (r+s) r : ℂ) • symmetricChartEquiv c
          (show CoefficientBaseChange (Depth.RB (r+s)) (symmetricPower (r+s)) A
            from 1 ⊗ₜ[Depth.RB (r+s)] p) := by
  rw [symmetricCoproductComponent_tensorBlock,map_smul,symmetricTensorBlock_chart]

end KhanSL2.SymmetricFamily
