module

public import KhanSL2.Macdonald.RootMonomialEmbeddings
public import KhanSL2.Macdonald.RootOddShift
public import KhanSL2.Macdonald.RootEvenShift

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Actual multiplication embeds each one-color exterior/symmetric bidegree in
the free Macdonald source, retaining the original raising derivations. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald
open SymmetricFamily PolynomialBGG

abbrev RootFreeBidegree (q r : ℕ) :=
  (⋀[ℂ]^q (Polynomial ℂ)) ⊗[ℂ] RootEvenPower r

/-- The actual symmetric monomial basis in the even polynomial power. -/
def rootEvenPowerBasis (r : ℕ) : Module.Basis (DegreeExponent ℕ r) ℂ (RootEvenPower r) :=
  Finsupp.basisSingleOne.map (rootEvenExponentEquiv r).symm

/-- The uncolored free coordinates in actual exterior/symmetric algebra powers. -/
def freeBidegreeSourceEquiv (q r : ℕ) :
    (FreeBidegreeIndex q r →₀ ℂ) ≃ₗ[ℂ] RootFreeBidegree q r :=
  (Finsupp.domLCongr (freeBidegreeIndexEquiv q r)).trans
    (((Polynomial.basisMonomials ℂ).exteriorPower q).tensorProduct
      (rootEvenPowerBasis r)).repr.symm

/-- Original multiplication of the actual even and odd generator embeddings. -/
def rootFreeBidegreeRaw (q r : ℕ) : RootFreeBidegree q r →ₗ[ℂ] StrongMacdonald.W :=
  (LinearMap.mul' ℂ StrongMacdonald.W).comp
    ((TensorProduct.map
      (rootEvenEmbedding.toLinearMap.comp (RootEvenPower r).subtype)
      (rootOddStrongEmbedding.toLinearMap.comp
        (ExteriorAlgebra.exteriorPower ℂ q (Polynomial ℂ)).subtype)).comp
          (TensorProduct.comm ℂ (⋀[ℂ]^q (Polynomial ℂ)) (RootEvenPower r)).toLinearMap)

@[simp] theorem rootFreeBidegreeRaw_tmul (q r : ℕ)
    (x : ⋀[ℂ]^q (Polynomial ℂ)) (p : RootEvenPower r) :
    rootFreeBidegreeRaw q r (x ⊗ₜ[ℂ] p) =
      rootEvenEmbedding p.val * rootOddStrongEmbedding x.val := rfl

theorem rootFreeBidegreeRaw_mem (q r : ℕ) (v : RootFreeBidegree q r) :
    rootFreeBidegreeRaw q r v ∈ strongFree := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | tmul x p =>
    change StrongMacdonald.projFull (rootEvenEmbedding p.val * rootOddStrongEmbedding x.val) = _
    rw [map_mul]
    have hp : StrongMacdonald.projFull (rootEvenEmbedding p.val) = rootEvenEmbedding p.val :=
      rootEvenEmbedding_mem_free p.val
    have hx : StrongMacdonald.projFull (rootOddStrongEmbedding x.val) = rootOddStrongEmbedding x.val :=
      rootOddStrongEmbedding_mem_free x.val
    rw [hp,hx]
    rfl

/-- The actual bidegree product, with values in the proved free subspace. -/
def rootFreeBidegreeMap (q r : ℕ) : RootFreeBidegree q r →ₗ[ℂ] strongFree :=
  (rootFreeBidegreeRaw q r).codRestrict strongFree (rootFreeBidegreeRaw_mem q r)

/-- Weighted root raising on the actual exterior/symmetric tensor model. -/
def rootFreeBidegreeShift (m q r : ℕ) : Module.End ℂ (RootFreeBidegree q r) :=
  TensorProduct.map (exteriorDeriv q (LinearMap.mulLeft ℂ ((Polynomial.X : Polynomial ℂ)^m)))
    LinearMap.id + (2 : ℂ) • TensorProduct.map LinearMap.id (rootEvenShiftEnd m r)

/-- The concrete bidegree embedding intertwines the concrete free raising map. -/
theorem rootFreeBidegreeMap_shift (m q r : ℕ) (v : RootFreeBidegree q r) :
    rootFreeBidegreeMap q r (rootFreeBidegreeShift m q r v) =
      strongFreeRaiseEnd m (rootFreeBidegreeMap q r v) := by
  apply Subtype.ext
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,Submodule.coe_add,hu,hv]
  | tmul x p =>
    change rootFreeBidegreeRaw q r (rootFreeBidegreeShift m q r (x ⊗ₜ[ℂ] p)) =
      strongFreeRaise m (rootEvenEmbedding p.val * rootOddStrongEmbedding x.val)
    simp only [rootFreeBidegreeShift,LinearMap.add_apply,LinearMap.smul_apply,
      TensorProduct.map_tmul,LinearMap.id_apply,map_add,map_smul,rootFreeBidegreeRaw_tmul]
    rw [(strongFreeRaise_homDer m).zero_mul_apply,rootEvenEmbedding_shift,
      rootOddStrongEmbedding_shift]
    rw [rootEvenShiftEnd_val,smul_mul_assoc,add_comm]
    rfl

end KhanSL2.Macdonald
