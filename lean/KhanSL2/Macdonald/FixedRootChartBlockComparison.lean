module

public import KhanSL2.Macdonald.WeightedRootFactorizationComponent
public import KhanSL2.Macdonald.SpecializedHomologyCoproduct

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped TensorProduct DirectSum
namespace KhanSL2.Macdonald
open Factorization WeightedRootModel
open scoped WeightedFactorScalars FactorHomologyScalars

variable {s s₁ s₂ q₁ q₂ r₁ r₂ : ℕ} {A : Type} [CommRing A] [Algebra ℂ A]
variable [Algebra (Depth.RB s) A] [IsScalarTower ℂ (Depth.RB s) A]
variable (c : Collision.ChartData s s₁ s₂ A)

/-- The canonical first allocation inside any presentation of the fixed total degree. -/
def fixedFirstRootAllocation (hb : q₁+2*r₁=s₁) :
    OrbitIndex (q₁+q₂) (r₁+r₂) s₁ :=
  ⟨(q₁,r₁),Nat.le_add_right _ _,Nat.le_add_right _ _,hb⟩

/-- Arithmetic transport identifies the original first orbit factor with its specified pair of factors. -/
def fixedFirstRootFactorEquiv (hd : 2*(r₁+r₂)+(q₁+q₂)=s) (hb : q₁+2*r₁=s₁) :
    FixedRootOrbitFactor c ⟨(q₁+q₂,r₁+r₂),hd⟩ (fixedFirstRootAllocation hb) ≃ₗ[A]
      FactorSignedModule q₁ r₁ c.f₁ ⊗[A] FactorSignedModule q₂ r₂ c.f₂ := by
  change (FactorSignedModule q₁ r₁ c.f₁ ⊗[A]
    FactorSignedModule ((q₁+q₂)-q₁) ((r₁+r₂)-r₁) c.f₂) ≃ₗ[A] _
  rw [Nat.add_sub_cancel_left,Nat.add_sub_cancel_left]

/-- In every fixed input block, literal normalized chart restriction equals the specified normalized root coproduct. -/
theorem fixedRootBlockChartEquiv_first (htotal : s₁+s₂=s)
    (hd : 2*(r₁+r₂)+(q₁+q₂)=s) (hb : q₁+2*r₁=s₁)
    (x : RootHomologyModel (q₁+q₂) (r₁+r₂)) :
    fixedFirstRootFactorEquiv c hd hb
      (fixedRootBlockChartEquiv c htotal ⟨(q₁+q₂,r₁+r₂),hd⟩
        (1 ⊗ₜ[Depth.RB s] fixedSignedRootBlockEquiv s ⟨(q₁+q₂,r₁+r₂),hd⟩ x)
        (fixedFirstRootAllocation hb)) =
      rootFactorizationNormalization (q₁+q₂) (r₁+r₂) q₁ r₁ •
        weightedRootHomologyTensorUnit q₁ q₂ r₁ r₂ c.f₁ c.f₂
          (rootHomologyNormalizedBlock q₁ q₂ r₁ r₂ x) := by
  have hs : s=(q₁+q₂)+2*(r₁+r₂) := by omega
  cases hs
  have hs₁ : s₁=q₁+2*r₁ := by omega
  cases hs₁
  have hs₂ : s₂=q₂+2*r₂ := by omega
  cases hs₂
  change firstOrbitFactorEquiv c
    (algebraMap ℂ A (rootFactorizationNormalization (q₁+q₂) (r₁+r₂) q₁ r₁) •
      signedInvariantFactorizationEquiv c htotal
        (1 ⊗ₜ[Depth.RB ((q₁+q₂)+2*(r₁+r₂))] rootHomologyModelEquiv (q₁+q₂) (r₁+r₂) x)
        (firstWeightedOrbitIndex q₁ q₂ r₁ r₂)) = _
  rw [map_smul,← rootHomologyNormalizedBlock_factorization c x]
  exact IsScalarTower.algebraMap_smul A _ _

/-- The coordinate chart equivalence and original specialized coproduct have the same fixed root component. -/
theorem normalizedHomologyRootChartEquiv_unit_component {t₁ t₂ : ℕ}
    [Algebra (Depth.RB (t₁+t₂)) A] [IsScalarTower ℂ (Depth.RB (t₁+t₂)) A]
    (c : Collision.ChartData (t₁+t₂) t₁ t₂ A)
    (h : TotalHomology (symmetricPower (t₁+t₂)))
    (d : RootHomologyDegrees t₁ × RootHomologyDegrees t₂) :
    factorSymmetricHomologyTensorRootEquiv t₁ t₂ c.f₁ c.f₂
      (normalizedHomologyRootChartEquiv c (1 ⊗ₜ[Depth.RB (t₁+t₂)] h)) d =
    factorSymmetricHomologyTensorRootEquiv t₁ t₂ c.f₁ c.f₂
      (specializedNormalizedHomologyCoproduct t₁ t₂ c.f₁ c.f₂ h) d := by
  rw [normalizedHomologyRootChartEquiv_tmul_component,specializedNormalizedHomologyCoproduct_rootBlock]
  exact fixedRootBlockChartEquiv_first c rfl
    (rootDegreeSum d.1 d.2).property (by have ht:=d.1.property; omega)
    (fixedRootHomologyComponent (t₁+t₂) (rootDegreeSum d.1 d.2) h)

end KhanSL2.Macdonald
