module

public import KhanSL2.Macdonald.StrongBridgeRootAction
public import KhanSL2.Macdonald.RootFreeCoproductNaturality
public import KhanSL2.Factorization.ExteriorShuffleComponents
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped TensorProduct DirectSum
namespace KhanSL2.Macdonald
open SymmetricFamily

/-- The component of the already specified free root equivalence. -/
def strongFreeRootProjection (d : ℕ × ℕ) : strongFree →ₗ[ℂ] RootHomologyModel d.1 d.2 :=
  (DFinsupp.lapply d).comp strongFreeRootEquiv.toLinearMap

/-- The same actual component, in exterior/symmetric powers. -/
def strongFreeBidegreeProjection (q r : ℕ) : strongFree →ₗ[ℂ] RootFreeBidegree q r :=
  (rootFreeToRootEquiv q r).symm.toLinearMap.comp (strongFreeRootProjection (q,r))

abbrev RootMixed := ExteriorAlgebra ℂ (Polynomial ℂ) ⊗[ℂ] RootEvenPolynomial

/-- Inclusion into the uncolored exterior/symmetric tensor algebra. -/
def rootBidegreeValue (q r : ℕ) : RootFreeBidegree q r →ₗ[ℂ] RootMixed :=
  TensorProduct.map (ExteriorAlgebra.exteriorPower ℂ q (Polynomial ℂ)).subtype (RootEvenPower r).subtype

/-- The uncolored mixed algebra enters the original free model by its original generator maps. -/
def rootMixedFreeMap : RootMixed →ₗ[ℂ] strongFree :=
  strongFreeRetraction.comp ((TensorProduct.map rootEvenPolynomialInclusion.toLinearMap
    rootOddExterior.toLinearMap).comp (TensorProduct.comm ℂ _ _).toLinearMap)

@[simp] theorem rootMixedFreeMap_bidegree (q r : ℕ) (x : RootFreeBidegree q r) :
    rootMixedFreeMap (rootBidegreeValue q r x) = rootFreeBidegreeMap q r x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add,ha,hb]
  | tmul a b =>
    change strongFreeRetraction (rootEvenPolynomialInclusion b.val ⊗ₜ[ℂ] rootOddExterior a.val) = _
    rw [← strongFreeEmbedding_bidegree_tmul,strongFreeRetraction_embedding]

@[simp] theorem strongFreeBidegreeProjection_same (q r : ℕ) (x : RootFreeBidegree q r) :
    strongFreeBidegreeProjection q r (rootFreeBidegreeMap q r x) = x := by
  change (rootFreeToRootEquiv q r).symm
    ((strongFreeRootEquiv (rootFreeBidegreeMap q r x)) (q,r)) = x
  rw [strongFreeRootEquiv_bidegreeMap]
  change (rootFreeToRootEquiv q r).symm
    ((DFinsupp.single (β := fun d : ℕ × ℕ => RootHomologyModel d.1 d.2) (q,r) (rootFreeToRootEquiv q r x)) (q,r)) = x
  rw [DFinsupp.single_eq_same,LinearEquiv.symm_apply_apply]

theorem strongFreeBidegreeProjection_other (q r q' r' : ℕ) (h : (q',r') ≠ (q,r))
    (x : RootFreeBidegree q' r') :
    strongFreeBidegreeProjection q r (rootFreeBidegreeMap q' r' x) = 0 := by
  change (rootFreeToRootEquiv q r).symm
    ((strongFreeRootEquiv (rootFreeBidegreeMap q' r' x)) (q,r)) = 0
  rw [strongFreeRootEquiv_bidegreeMap]
  change (rootFreeToRootEquiv q r).symm
    ((DFinsupp.single (β := fun d : ℕ × ℕ => RootHomologyModel d.1 d.2) (q',r') (rootFreeToRootEquiv q' r' x)) (q,r)) = 0
  rw [DFinsupp.single_eq_of_ne h.symm, LinearEquiv.map_zero]

/-- The concrete uncolored degree projector. -/
def rootMixedDegreeProjection (q r : ℕ) : Module.End ℂ RootMixed :=
  TensorProduct.map (Factorization.ExteriorShuffle.degreeProjection (Polynomial ℂ) q)
    (MvPolynomial.homogeneousComponent r)

theorem rootMixedDegreeProjection_bidegree (q r q' r' : ℕ) (x : RootFreeBidegree q' r') :
    rootMixedDegreeProjection q r (rootBidegreeValue q' r' x) =
      if (q',r')=(q,r) then rootBidegreeValue q' r' x else 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add,ha,hb]; split_ifs <;> simp
  | tmul a b =>
    change Factorization.ExteriorShuffle.degreeProjection (Polynomial ℂ) q a.val ⊗ₜ[ℂ]
      MvPolynomial.homogeneousComponent r b.val =
        if (q',r')=(q,r) then a.val ⊗ₜ[ℂ] b.val else 0
    rw [Factorization.ExteriorShuffle.degreeProjection_of_mem (Polynomial ℂ) q q' a.val a.property,
      MvPolynomial.homogeneousComponent_of_mem b.property]
    by_cases hq : q'=q <;> by_cases hr : r=r' <;> simp [hq,hr,Ne.symm]

/-- Agreement of coordinate projection with the original homogeneous projections on each homogeneous tensor. -/
theorem strongFreeBidegreeProjection_rootMixed_bidegree (q r q' r' : ℕ)
    (x : RootFreeBidegree q' r') :
    rootBidegreeValue q r (strongFreeBidegreeProjection q r
      (rootMixedFreeMap (rootBidegreeValue q' r' x))) =
      rootMixedDegreeProjection q r (rootBidegreeValue q' r' x) := by
  rw [rootMixedFreeMap_bidegree,rootMixedDegreeProjection_bidegree]
  by_cases h : (q',r')=(q,r)
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
    rw [if_pos rfl,strongFreeBidegreeProjection_same]
  · rw [if_neg h,strongFreeBidegreeProjection_other q r q' r' h,map_zero]

/-- The original coordinate projection is precisely the canonical homogeneous projection on the uncolored model. -/
theorem strongFreeBidegreeProjection_rootMixed (q r : ℕ) (x : RootMixed) :
    rootBidegreeValue q r (strongFreeBidegreeProjection q r (rootMixedFreeMap x)) =
      rootMixedDegreeProjection q r x := by
  have h : (rootBidegreeValue q r).comp ((strongFreeBidegreeProjection q r).comp rootMixedFreeMap) =
      rootMixedDegreeProjection q r := by
    apply ((Polynomial.basisMonomials ℂ).ExteriorAlgebra.tensorProduct
      (MvPolynomial.basisMonomials ℕ ℂ)).ext
    rintro ⟨s,e⟩
    rw [Module.Basis.tensorProduct_apply']
    let a : ⋀[ℂ]^s.card (Polynomial ℂ) :=
      (Polynomial.basisMonomials ℂ).exteriorPower s.card ⟨s,rfl⟩
    let b : RootEvenPower e.degree := ⟨MvPolynomial.monomial e 1,
      MvPolynomial.isHomogeneous_monomial 1 rfl⟩
    have ha : (Polynomial.basisMonomials ℂ).ExteriorAlgebra s = a.val :=
      ExteriorAlgebra.basis_eq_coe_basis _ ⟨s,rfl⟩
    rw [ha]
    exact strongFreeBidegreeProjection_rootMixed_bidegree q r s.card e.degree (a ⊗ₜ[ℂ] b)
  exact LinearMap.congr_fun h x

theorem rootBidegreeValue_injective (q r : ℕ) : Function.Injective (rootBidegreeValue q r) := by
  intro x y h
  have hh := congrArg (fun z => strongFreeBidegreeProjection q r (rootMixedFreeMap z)) h
  simpa only [rootMixedFreeMap_bidegree,strongFreeBidegreeProjection_same] using hh

end KhanSL2.Macdonald


