module

public import KhanSL2.Macdonald.StrongBridgeFixedCoproductComponents
public import KhanSL2.Macdonald.StrongBridgeHomologyCoproductCompatibility
public import KhanSL2.Macdonald.RootCoproductOffBidegree
public import KhanSL2.Macdonald.RootFactorizationNormalization

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped TensorProduct DirectSum
namespace KhanSL2.Macdonald
open Factorization

/-- The fixed source root degree obtained by adding the two actual output root degrees. -/
def rootDegreeSum {s₁ s₂ : ℕ} (d₁ : RootHomologyDegrees s₁) (d₂ : RootHomologyDegrees s₂) :
    RootHomologyDegrees (s₁+s₂) :=
  ⟨(d₁.val.1+d₂.val.1,d₁.val.2+d₂.val.2),by
    have h₁ := d₁.property
    have h₂ := d₂.property
    omega⟩

/-- The total root component is the existing free-root component of the original homology equivalence. -/
theorem totalRootHomologyComponent_free (d : ℕ × ℕ) (h : TotalHomology SymmetricCoefficients) :
    totalRootHomologyComponent d h = strongFreeRootProjection d (strongTotalHomologyFreeEquiv h) := rfl

/-- The actual fixed-degree inclusion preserves its original root components. -/
theorem totalRootHomologyComponent_inclusion (s : ℕ) (d : RootHomologyDegrees s)
    (h : TotalHomology (symmetricPower s)) :
    totalRootHomologyComponent d.val (symmetricHomologyInclusion s h) =
      fixedRootHomologyComponent s d h := by
  change strongTotalHomologyRootEquiv (symmetricHomologyInclusion s h) d.val =
    symmetricPowerRootEquiv s h d
  rw [strongTotalHomologyRootEquiv_symmetricInclusion,fixedRootInclusion_apply]

/-- Exact root-block formula for the original total relative CE homology coproduct. -/
theorem symmetricHomologyCoproduct_rootBlock (q₁ q₂ r₁ r₂ : ℕ)
    (h : TotalHomology SymmetricCoefficients) :
    TensorProduct.map (totalRootHomologyComponent (q₁,r₁)) (totalRootHomologyComponent (q₂,r₂))
      (symmetricHomologyCoproduct h) =
      ((Nat.choose (q₁+q₂) q₁ : ℂ) * (Nat.choose (r₁+r₂) r₁ : ℂ)) •
        rootHomologyNormalizedBlock q₁ q₂ r₁ r₂
          (totalRootHomologyComponent (q₁+q₂,r₁+r₂) h) := by
  have hm (d : ℕ × ℕ) : (strongFreeRootProjection d).comp strongTotalHomologyFreeEquiv.toLinearMap =
      totalRootHomologyComponent d := rfl
  have hh := congrArg (TensorProduct.map (strongFreeRootProjection (q₁,r₁))
      (strongFreeRootProjection (q₂,r₂))) (strongTotalHomologyFreeEquiv_coproduct h)
  change ((TensorProduct.map (strongFreeRootProjection (q₁,r₁)) (strongFreeRootProjection (q₂,r₂))).comp
    (TensorProduct.map strongTotalHomologyFreeEquiv.toLinearMap strongTotalHomologyFreeEquiv.toLinearMap)) _ = _ at hh
  rw [← TensorProduct.map_comp,hm,hm,strongFreePrimitiveCoproduct_root_projection] at hh
  exact hh

/-- Exact odd/even binomial normalization in the actual fixed-degree homology coproduct. -/
theorem symmetricPowerHomologyCoproduct_rootBlock (s₁ s₂ : ℕ)
    (d₁ : RootHomologyDegrees s₁) (d₂ : RootHomologyDegrees s₂)
    (h : TotalHomology (symmetricPower (s₁+s₂))) :
    TensorProduct.map (fixedRootHomologyComponent s₁ d₁) (fixedRootHomologyComponent s₂ d₂)
      (symmetricPowerHomologyCoproduct s₁ s₂ h) =
      ((Nat.choose (d₁.val.1+d₂.val.1) d₁.val.1 : ℂ) *
        (Nat.choose (d₁.val.2+d₂.val.2) d₁.val.2 : ℂ)) •
        rootHomologyNormalizedBlock d₁.val.1 d₂.val.1 d₁.val.2 d₂.val.2
          (fixedRootHomologyComponent (s₁+s₂) (rootDegreeSum d₁ d₂) h) := by
  rw [symmetricPowerHomologyCoproduct_rootComponent,symmetricHomologyCoproduct_rootBlock]
  rw [← totalRootHomologyComponent_inclusion (s₁+s₂) (rootDegreeSum d₁ d₂)]
  rfl

/-- Normalize the original fixed coefficient coproduct by its coefficient-binomial factor. -/
def normalizedSymmetricPowerHomologyCoproduct (s₁ s₂ : ℕ) :
    TotalHomology (symmetricPower (s₁+s₂)) →ₗ[ℂ]
      TotalHomology (symmetricPower s₁) ⊗[ℂ] TotalHomology (symmetricPower s₂) :=
  (Nat.choose (s₁+s₂) s₁ : ℂ)⁻¹ • symmetricPowerHomologyCoproduct s₁ s₂

/-- Exact scalar on a pair of fixed root degrees. -/
theorem rootFactorizationNormalization_degreeSum {s₁ s₂ : ℕ}
    (d₁ : RootHomologyDegrees s₁) (d₂ : RootHomologyDegrees s₂) :
    rootFactorizationNormalization (d₁.val.1+d₂.val.1) (d₁.val.2+d₂.val.2) d₁.val.1 d₁.val.2 =
      (Nat.choose (s₁+s₂) s₁ : ℂ)⁻¹ *
        ((Nat.choose (d₁.val.1+d₂.val.1) d₁.val.1 : ℂ) *
          (Nat.choose (d₁.val.2+d₂.val.2) d₁.val.2 : ℂ)) := by
  have h₁ : d₁.val.1+2*d₁.val.2=s₁ := by have h := d₁.property; omega
  have hsum : (d₁.val.1+d₂.val.1)+2*(d₁.val.2+d₂.val.2)=s₁+s₂ := by
    have h₂ := d₂.property
    omega
  rw [rootFactorizationNormalization,h₁,hsum,mul_assoc]

/-- The actual normalized homology coproduct has exactly the invertible weighted-root normalization. -/
theorem normalizedSymmetricPowerHomologyCoproduct_rootBlock (s₁ s₂ : ℕ)
    (d₁ : RootHomologyDegrees s₁) (d₂ : RootHomologyDegrees s₂)
    (h : TotalHomology (symmetricPower (s₁+s₂))) :
    TensorProduct.map (fixedRootHomologyComponent s₁ d₁) (fixedRootHomologyComponent s₂ d₂)
      (normalizedSymmetricPowerHomologyCoproduct s₁ s₂ h) =
      rootFactorizationNormalization (d₁.val.1+d₂.val.1) (d₁.val.2+d₂.val.2) d₁.val.1 d₁.val.2 •
        rootHomologyNormalizedBlock d₁.val.1 d₂.val.1 d₁.val.2 d₂.val.2
          (fixedRootHomologyComponent (s₁+s₂) (rootDegreeSum d₁ d₂) h) := by
  change TensorProduct.map _ _ ((Nat.choose (s₁+s₂) s₁ : ℂ)⁻¹ •
    symmetricPowerHomologyCoproduct s₁ s₂ h) = _
  rw [map_smul,symmetricPowerHomologyCoproduct_rootBlock,smul_smul,
    rootFactorizationNormalization_degreeSum]

/-- Literal weighted-root diagram for the actual normalized fixed homology coproduct. -/
theorem normalizedSymmetricPowerHomologyCoproduct_weighted (s₁ s₂ : ℕ)
    (d₁ : RootHomologyDegrees s₁) (d₂ : RootHomologyDegrees s₂)
    (h : TotalHomology (symmetricPower (s₁+s₂))) :
    TensorProduct.map (rootHomologyWeightedMap d₁.val.1 d₁.val.2)
      (rootHomologyWeightedMap d₂.val.1 d₂.val.2)
      (TensorProduct.map (fixedRootHomologyComponent s₁ d₁) (fixedRootHomologyComponent s₂ d₂)
        (normalizedSymmetricPowerHomologyCoproduct s₁ s₂ h)) =
      rootFactorizationNormalization (d₁.val.1+d₂.val.1) (d₁.val.2+d₂.val.2) d₁.val.1 d₁.val.2 •
        weightedRootPolynomialBlock d₁.val.1 d₂.val.1 d₁.val.2 d₂.val.2
          (rootHomologyWeightedMap (d₁.val.1+d₂.val.1) (d₁.val.2+d₂.val.2)
            (fixedRootHomologyComponent (s₁+s₂) (rootDegreeSum d₁ d₂) h)) := by
  rw [normalizedSymmetricPowerHomologyCoproduct_rootBlock,map_smul,rootHomologyNormalizedBlock_weighted]

end KhanSL2.Macdonald
