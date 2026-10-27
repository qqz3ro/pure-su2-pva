module

public import KhanSL2.Factorization.WeightedRootModelUniversal

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators TensorProduct
namespace KhanSL2.Factorization.WeightedRootModel
open WeightedRoots

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- The actual weighted-root algebra of a specified polynomial through its
prescribed elementary coefficient map. -/
def FactorRoots (q r : ℕ) (f : A[X]) : Type :=
  letI : Algebra (Depth.RB (q+2*r)) A := (Collision.coeffHom (q+2*r) f).toRingHom.toAlgebra
  WeightedBase q r A

instance (q r : ℕ) (f : A[X]) : CommRing (FactorRoots q r f) := by
  unfold FactorRoots
  infer_instance
instance (q r : ℕ) (f : A[X]) : Algebra A (FactorRoots q r f) := by
  unfold FactorRoots
  infer_instance

def factorRoot (q r : ℕ) (f : A[X]) (i : Fin q ⊕ Fin r) : FactorRoots q r f :=
  letI : Algebra (Depth.RB (q+2*r)) A := (Collision.coeffHom (q+2*r) f).toRingHom.toAlgebra
  baseRoot q r A i

/-- The actual weighted root generators satisfy the full polynomial identity. -/
theorem factorRoot_product (q r : ℕ) (f : A[X]) (hf : f.Monic) (hn : f.natDegree = q+2*r) :
    rootProduct (factorRoot q r f) (rootWeight q r) Finset.univ =
      f.map (algebraMap A (FactorRoots q r f)) := by
  let : Algebra (Depth.RB (q+2*r)) A := (Collision.coeffHom (q+2*r) f).toRingHom.toAlgebra
  change rootProduct (baseRoot q r A) (rootWeight q r) Finset.univ =
    f.map (algebraMap A (WeightedBase q r A))
  rw [← univPoly_map_baseRoot,IsScalarTower.algebraMap_eq (Depth.RB (q+2*r)) A (WeightedBase q r A),
    ← Polynomial.map_map]
  exact congrArg (Polynomial.map (algebraMap A (WeightedBase q r A)))
    (Collision.univPoly_map_coeffHom hf hn)

/-- Universal evaluation at an actual weighted root factorization. -/
def factorRootsLift (q r : ℕ) (f : A[X]) (hf : f.Monic) (hn : f.natDegree = q+2*r)
    {S : Type*} [CommRing S] [Algebra A S] (x : Fin q ⊕ Fin r → S)
    (hx : rootProduct x (rootWeight q r) Finset.univ = f.map (algebraMap A S)) :
    FactorRoots q r f →ₐ[A] S := by
  letI : Algebra (Depth.RB (q+2*r)) A := (Collision.coeffHom (q+2*r) f).toRingHom.toAlgebra
  letI : Algebra (Depth.RB (q+2*r)) S :=
    ((algebraMap A S).comp (algebraMap (Depth.RB (q+2*r)) A)).toAlgebra
  letI : IsScalarTower (Depth.RB (q+2*r)) A S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact rootBaseEvaluation q r A x (by
    rw [IsScalarTower.algebraMap_eq (Depth.RB (q+2*r)) A S,← Polynomial.map_map]
    exact (congrArg (Polynomial.map (algebraMap A S))
      (Collision.univPoly_map_coeffHom hf hn)).trans hx.symm)

@[simp] theorem factorRootsLift_factorRoot (q r : ℕ) (f : A[X])
    (hf : f.Monic) (hn : f.natDegree = q+2*r) {S : Type*} [CommRing S] [Algebra A S]
    (x : Fin q ⊕ Fin r → S) (hx) (i : Fin q ⊕ Fin r) :
    factorRootsLift q r f hf hn x hx (factorRoot q r f i) = x i := by
  let : Algebra (Depth.RB (q+2*r)) A := (Collision.coeffHom (q+2*r) f).toRingHom.toAlgebra
  let : Algebra (Depth.RB (q+2*r)) S :=
    ((algebraMap A S).comp (algebraMap (Depth.RB (q+2*r)) A)).toAlgebra
  let : IsScalarTower (Depth.RB (q+2*r)) A S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  change rootBaseEvaluation q r A x _ (baseRoot q r A i) = x i
  exact rootBaseEvaluation_baseRoot q r A x _ i

/-- Maps out of the actual weighted root algebra are determined by its root variables. -/
theorem factorRootsAlgHom_ext (q r : ℕ) (f : A[X]) {S : Type*} [CommRing S] [Algebra A S]
    {g h : FactorRoots q r f →ₐ[A] S}
    (hx : ∀ i : Fin q ⊕ Fin r, g (factorRoot q r f i) = h (factorRoot q r f i)) : g = h := by
  let : Algebra (Depth.RB (q+2*r)) A := (Collision.coeffHom (q+2*r) f).toRingHom.toAlgebra
  exact rootBaseAlgHom_ext q r A hx

end KhanSL2.Factorization.WeightedRootModel
