module

public import KhanSL2.Factorization.FiniteBGGTransferNaturality
public import KhanSL2.PolynomialBGG.ProjectiveModelAction

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped TensorProduct
namespace KhanSL2.Factorization.BGGTransfer
open BGG BGGBridge SymmetricFamily PolynomialBGG Conditional

attribute [local instance] harmonicModule harmonicIsScalarTower harmonicSMulCommClass

/-- Projection of the harmonic factor, keeping the actual exterior coefficients. -/
def exteriorHarmonicProj (B p : ℕ) : HarmN (⋀[ℂ]^B BGG.Current) →ₗ[ℂ] WindowModel B p :=
  TensorProduct.map (PositiveCE.standardHarmonicProjection p).toLinearMap LinearMap.id

def exteriorHarmonicIncl (B p : ℕ) : WindowModel B p →ₗ[ℂ] HarmN (⋀[ℂ]^B BGG.Current) :=
  TensorProduct.map (PositiveCE.standardHarmonicEmbedding p).toLinearMap LinearMap.id

theorem exteriorHarmonicProj_act (B p : ℕ) (x : G) (z : HarmN (⋀[ℂ]^B BGG.Current)) :
    exteriorHarmonicProj B p (actH (⋀[ℂ]^B BGG.Current) x z) =
      windowAct B p x (exteriorHarmonicProj B p z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw]
  | tmul h n =>
    simp only [exteriorHarmonicProj,actH,windowAct,diag_tmul,map_add,
      TensorProduct.map_tmul,LinearMap.id_apply,LieModule.toEnd_apply_apply]
    change PositiveCE.standardHarmonicProjection p ⁅x,h⁆ ⊗ₜ[ℂ] n +
      PositiveCE.standardHarmonicProjection p h ⊗ₜ[ℂ] ⁅constant x,n⁆ = _
    rw [(PositiveCE.standardHarmonicProjection p).map_lie]
    rfl

theorem exteriorHarmonicIncl_act (B p : ℕ) (x : G) (z : WindowModel B p) :
    exteriorHarmonicIncl B p (windowAct B p x z) =
      actH (⋀[ℂ]^B BGG.Current) x (exteriorHarmonicIncl B p z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw]
  | tmul h n =>
    simp only [exteriorHarmonicIncl,actH,windowAct,diag_tmul,map_add,
      TensorProduct.map_tmul,LinearMap.id_apply,LieModule.toEnd_apply_apply]
    exact congrArg (fun h0 : PositiveCE.Harmonic => h0 ⊗ₜ[ℂ] n +
      PositiveCE.standardHarmonicEmbedding p h ⊗ₜ[ℂ] ⁅constant x,n⁆)
      ((PositiveCE.standardHarmonicEmbedding p).map_lie x h)

def exteriorHarmonicProjQ (B p : ℕ) :
    HarmonicQuotient (⋀[ℂ]^B BGG.Current) →ₗ[ℂ] WindowCoinvariants B p :=
  (relH (⋀[ℂ]^B BGG.Current)).mapQ (windowRelations B p) (exteriorHarmonicProj B p)
    (le_comap_of_commute _ _ _ (exteriorHarmonicProj_act B p))

def exteriorHarmonicInclQ (B p : ℕ) :
    WindowCoinvariants B p →ₗ[ℂ] HarmonicQuotient (⋀[ℂ]^B BGG.Current) :=
  (windowRelations B p).mapQ (relH (⋀[ℂ]^B BGG.Current)) (exteriorHarmonicIncl B p)
    (le_comap_of_commute _ _ _ (exteriorHarmonicIncl_act B p))

@[simp] theorem exteriorHarmonicProjQ_inclQ (B p : ℕ) (z : WindowCoinvariants B p) :
    exteriorHarmonicProjQ B p (exteriorHarmonicInclQ B p z) = z := by
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    change (windowRelations B p).mkQ (exteriorHarmonicProj B p (exteriorHarmonicIncl B p z)) =
      (windowRelations B p).mkQ z
    congr 1
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add,hz,hw]
    | tmul h n => simp [exteriorHarmonicProj,exteriorHarmonicIncl]

theorem exteriorHarmonicIncl_proj_of_mem (B p : ℕ) (z : HarmN (⋀[ℂ]^B BGG.Current))
    (hz : z ∈ tensorLeft (degH p)) :
    exteriorHarmonicIncl B p (exteriorHarmonicProj B p z) = z := by
  obtain ⟨w,rfl⟩ := hz
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw]
  | tmul h n =>
    change PositiveCE.standardHarmonicEmbedding p (PositiveCE.standardHarmonicProjection p h.val)
      ⊗ₜ[ℂ] n = h.val ⊗ₜ[ℂ] n
    rw [PositiveCE.standardHarmonicEmbedding_projection_of_mem p h.val h.property]

theorem exteriorHarmonicInclQ_mem (B p : ℕ) (z : WindowCoinvariants B p) :
    exteriorHarmonicInclQ B p z ∈ harmonicDegree (CoefficientRing B) (⋀[ℂ]^B BGG.Current) p := by
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    refine ⟨exteriorHarmonicIncl B p z,?_,rfl⟩
    change exteriorHarmonicIncl B p z ∈ tensorLeft (N := ⋀[ℂ]^B BGG.Current) (degH p)
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => rw [map_add]; exact Submodule.add_mem _ hz hw
    | tmul h n =>
      exact tmul_mem_tensorLeft ((PositiveCE.harmonicDegreeStandardEquiv p).symm h).property n

theorem exteriorHarmonicInclQ_projQ_of_mem (B p : ℕ)
    (z : harmonicDegree (CoefficientRing B) (⋀[ℂ]^B BGG.Current) p) :
    exteriorHarmonicInclQ B p (exteriorHarmonicProjQ B p z.val) = z.val := by
  obtain ⟨w,hw,hz⟩ := z.property
  rw [← hz]
  change (relH (⋀[ℂ]^B BGG.Current)).mkQ
    (exteriorHarmonicIncl B p (exteriorHarmonicProj B p w)) = _
  rw [exteriorHarmonicIncl_proj_of_mem B p w hw]

/-- The harmonic-degree quotient is the actual previously proved window model. -/
def exteriorHarmonicWindowEquiv (B p : ℕ) :
    harmonicDegree (CoefficientRing B) (⋀[ℂ]^B BGG.Current) p ≃ₗ[ℂ] WindowCoinvariants B p where
  toFun z := exteriorHarmonicProjQ B p z.val
  invFun z := ⟨exteriorHarmonicInclQ B p z,exteriorHarmonicInclQ_mem B p z⟩
  left_inv z := Subtype.ext (exteriorHarmonicInclQ_projQ_of_mem B p z)
  right_inv := exteriorHarmonicProjQ_inclQ B p
  map_add' z w := (exteriorHarmonicProjQ B p).map_add z.val w.val
  map_smul' c z := (exteriorHarmonicProjQ B p).map_smul c z.val

end KhanSL2.Factorization.BGGTransfer



