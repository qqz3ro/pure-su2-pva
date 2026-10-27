module

public import KhanSL2.SymmetricFamily.RootUniversal

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Labelled roots of one monic polynomial, formed by the original coefficient
base change. The wrapper keeps the two different chart coefficient maps distinct. -/

noncomputable section
open Polynomial
open scoped BigOperators TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- The actual labelled-root algebra of a specified polynomial over A. -/
def FactorRoots (n : ℕ) (f : A[X]) : Type :=
  letI : Algebra (Depth.RB n) A := (Collision.coeffHom n f).toRingHom.toAlgebra
  RootBase n A

instance (n : ℕ) (f : A[X]) : CommRing (FactorRoots n f) := by
  unfold FactorRoots
  infer_instance

instance (n : ℕ) (f : A[X]) : Algebra A (FactorRoots n f) := by
  unfold FactorRoots
  infer_instance

/-- The labelled root generators in the specified polynomial's root algebra. -/
def factorRoot (n : ℕ) (f : A[X]) (i : Fin n) : FactorRoots n f :=
  letI : Algebra (Depth.RB n) A := (Collision.coeffHom n f).toRingHom.toAlgebra
  baseRoot n A i

/-- These actual roots multiply to the specified monic polynomial. -/
theorem factorRoot_product (n : ℕ) (f : A[X]) (hf : f.Monic) (hn : f.natDegree = n) :
    ∏ i : Fin n, (Polynomial.X - Polynomial.C (factorRoot n f i)) =
      f.map (algebraMap A (FactorRoots n f)) := by
  let : Algebra (Depth.RB n) A := (Collision.coeffHom n f).toRingHom.toAlgebra
  change (∏ i : Fin n, ((Polynomial.X : Polynomial (RootBase n A)) - Polynomial.C (baseRoot n A i))) =
    f.map (algebraMap A (RootBase n A))
  rw [← univPoly_map_baseRoot,
    IsScalarTower.algebraMap_eq (Depth.RB n) A (RootBase n A), ← Polynomial.map_map]
  exact congrArg (Polynomial.map (algebraMap A (RootBase n A)))
    (Collision.univPoly_map_coeffHom hf hn)

/-- Universal evaluation of the actual root algebra at any ordered root factorization. -/
def factorRootsLift (n : ℕ) (f : A[X]) (hf : f.Monic) (hn : f.natDegree = n)
    {S : Type*} [CommRing S] [Algebra A S] (x : Fin n → S)
    (hx : ∏ i : Fin n, (Polynomial.X - Polynomial.C (x i)) =
      f.map (algebraMap A S)) : FactorRoots n f →ₐ[A] S := by
  letI : Algebra (Depth.RB n) A := (Collision.coeffHom n f).toRingHom.toAlgebra
  letI : Algebra (Depth.RB n) S :=
    ((algebraMap A S).comp (algebraMap (Depth.RB n) A)).toAlgebra
  letI : IsScalarTower (Depth.RB n) A S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact rootBaseEvaluation n A x (by
    rw [IsScalarTower.algebraMap_eq (Depth.RB n) A S, ← Polynomial.map_map]
    exact (congrArg (Polynomial.map (algebraMap A S))
      (Collision.univPoly_map_coeffHom hf hn)).trans hx.symm)

@[simp] theorem factorRootsLift_factorRoot (n : ℕ) (f : A[X])
    (hf : f.Monic) (hn : f.natDegree = n) {S : Type*} [CommRing S] [Algebra A S]
    (x : Fin n → S) (hx) (i : Fin n) :
    factorRootsLift n f hf hn x hx (factorRoot n f i) = x i := by
  let : Algebra (Depth.RB n) A := (Collision.coeffHom n f).toRingHom.toAlgebra
  let : Algebra (Depth.RB n) S :=
    ((algebraMap A S).comp (algebraMap (Depth.RB n) A)).toAlgebra
  let : IsScalarTower (Depth.RB n) A S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  change rootBaseEvaluation n A x _ (baseRoot n A i) = x i
  exact rootBaseEvaluation_baseRoot n A x _ i

/-- Equality on the ordered roots is enough to compare A-algebra maps. -/
theorem factorRootsAlgHom_ext (n : ℕ) (f : A[X]) {S : Type*} [CommRing S] [Algebra A S]
    {g h : FactorRoots n f →ₐ[A] S}
    (hx : ∀ i : Fin n, g (factorRoot n f i) = h (factorRoot n f i)) : g = h := by
  let : Algebra (Depth.RB n) A := (Collision.coeffHom n f).toRingHom.toAlgebra
  exact rootBaseAlgHom_ext n A hx

end KhanSL2.SymmetricFamily
