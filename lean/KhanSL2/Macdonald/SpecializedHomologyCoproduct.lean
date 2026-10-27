module

public import KhanSL2.Macdonald.HomologyRootChartComponents

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped TensorProduct DirectSum
namespace KhanSL2.Macdonald
open Factorization WeightedRootModel
open scoped WeightedFactorScalars FactorHomologyScalars

/-- The usual tensor/direct-sum equivalence has its literal component formula. -/
theorem tensorDirectSum_apply {R ι κ : Type*} [CommRing R] [DecidableEq ι] [DecidableEq κ]
    (M : ι → Type*) (N : κ → Type*) [∀ i, AddCommGroup (M i)] [∀ j, AddCommGroup (N j)]
    [∀ i, Module R (M i)] [∀ j, Module R (N j)]
    (x : ⨁ i, M i) (y : ⨁ j, N j) (i : ι) (j : κ) :
    TensorProduct.directSum R R M N (x ⊗ₜ[R] y) (i,j) = x i ⊗ₜ[R] y j := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x z hx hz =>
    rw [TensorProduct.add_tmul,map_add]
    change _ + _ = (x i+z i) ⊗ₜ[R] y j
    rw [TensorProduct.add_tmul,hx,hz]
  | of a x =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | add y z hy hz =>
      rw [TensorProduct.tmul_add,map_add]
      change _ + _ = ((DirectSum.of M a x) i) ⊗ₜ[R] (y j+z j)
      rw [TensorProduct.tmul_add,hy,hz]
    | of b y =>
      rw [← DirectSum.lof_eq_of R,← DirectSum.lof_eq_of R,TensorProduct.directSum_lof_tmul_lof]
      by_cases ha : a=i <;> by_cases hb : b=j
      · subst a; subst b; simp
      · subst a; simp [DirectSum.lof_eq_of,DirectSum.of_apply,hb,Ne.symm hb]
      · subst b; simp [DirectSum.lof_eq_of,DirectSum.of_apply,ha,Ne.symm ha]
      · simp [DirectSum.lof_eq_of,DirectSum.of_apply,ha,hb,Ne.symm ha,Ne.symm hb]

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- The original normalized homology coproduct followed by canonical specialization of each factor. -/
def specializedNormalizedHomologyCoproduct (s₁ s₂ : ℕ) (f₁ f₂ : Polynomial A) :
    TotalHomology (symmetricPower (s₁+s₂)) →ₗ[ℂ]
      FactorSymmetricHomology s₁ f₁ ⊗[A] FactorSymmetricHomology s₂ f₂ :=
  (SymmetricFamily.tensorOverMap (factorSymmetricHomologyUnit s₁ f₁)
    (factorSymmetricHomologyUnit s₂ f₂)).comp (normalizedSymmetricPowerHomologyCoproduct s₁ s₂)

/-- Componentwise compatibility of canonical factor specialization with original homology root coordinates. -/
theorem factorSymmetricHomologyTensorRootEquiv_specialize (s₁ s₂ : ℕ) (f₁ f₂ : Polynomial A)
    (z : TotalHomology (symmetricPower s₁) ⊗[ℂ] TotalHomology (symmetricPower s₂))
    (d : RootHomologyDegrees s₁ × RootHomologyDegrees s₂) :
    factorSymmetricHomologyTensorRootEquiv s₁ s₂ f₁ f₂
      (SymmetricFamily.tensorOverMap (factorSymmetricHomologyUnit s₁ f₁) (factorSymmetricHomologyUnit s₂ f₂) z) d =
      weightedRootHomologyTensorUnit d.1.val.1 d.2.val.1 d.1.val.2 d.2.val.2 f₁ f₂
        (TensorProduct.map (fixedRootHomologyComponent s₁ d.1) (fixedRootHomologyComponent s₂ d.2) z) := by
  classical
  rcases d with ⟨d₁,d₂⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw =>
    simp only [map_add]
    exact congrArg₂ (fun x y : FactorHomologyRootPair s₁ s₂ f₁ f₂ (d₁,d₂) => x+y) hz hw
  | tmul z w =>
    simp only [SymmetricFamily.tensorOverMap_tmul,factorSymmetricHomologyTensorRootEquiv,
      LinearEquiv.trans_apply,TensorProduct.congr_tmul,tensorDirectSum_apply,
      factorSymmetricHomologyRootEquiv_unit,TensorProduct.map_tmul,weightedRootHomologyTensorUnit,
      SymmetricFamily.tensorOverMap_tmul]

/-- The specified specialized coproduct has exactly the μ-scaled normalized root block in every component. -/
theorem specializedNormalizedHomologyCoproduct_rootBlock (s₁ s₂ : ℕ) (f₁ f₂ : Polynomial A)
    (h : TotalHomology (symmetricPower (s₁+s₂)))
    (d : RootHomologyDegrees s₁ × RootHomologyDegrees s₂) :
    factorSymmetricHomologyTensorRootEquiv s₁ s₂ f₁ f₂
      (specializedNormalizedHomologyCoproduct s₁ s₂ f₁ f₂ h) d =
      rootFactorizationNormalization (d.1.val.1+d.2.val.1) (d.1.val.2+d.2.val.2) d.1.val.1 d.1.val.2 •
        weightedRootHomologyTensorUnit d.1.val.1 d.2.val.1 d.1.val.2 d.2.val.2 f₁ f₂
          (rootHomologyNormalizedBlock d.1.val.1 d.2.val.1 d.1.val.2 d.2.val.2
            (fixedRootHomologyComponent (s₁+s₂) (rootDegreeSum d.1 d.2) h)) := by
  change factorSymmetricHomologyTensorRootEquiv s₁ s₂ f₁ f₂
    (SymmetricFamily.tensorOverMap _ _ (normalizedSymmetricPowerHomologyCoproduct s₁ s₂ h)) d = _
  rw [factorSymmetricHomologyTensorRootEquiv_specialize,
    normalizedSymmetricPowerHomologyCoproduct_rootBlock,map_smul]

end KhanSL2.Macdonald
