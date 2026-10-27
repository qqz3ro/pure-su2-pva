module

public import KhanSL2.Factorization.WeightedRootModelFactorAlgebra
public import KhanSL2.Factorization.WeightedRootModelChartAction

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped TensorProduct
namespace KhanSL2.Factorization.WeightedRootModel

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- Signed weighted-root coefficients over the exact coefficient map of f. -/
def FactorSignedModule (q r : ℕ) (f : A[X]) : Type :=
  letI : Algebra (Depth.RB (q+2*r)) A := (Collision.coeffHom (q+2*r) f).toRingHom.toAlgebra
  A ⊗[Depth.RB (q+2*r)] signedInvariantModule q r

instance (q r : ℕ) (f : A[X]) : AddCommGroup (FactorSignedModule q r f) := by
  unfold FactorSignedModule
  infer_instance
instance (q r : ℕ) (f : A[X]) : Module A (FactorSignedModule q r f) := by
  unfold FactorSignedModule
  infer_instance

/-- The original permutations on a specified weighted-root fibre algebra. -/
def factorRootAutomorphism (q r : ℕ) (f : A[X]) (g : BlockGroup q r) :
    FactorRoots q r f ≃ₐ[A] FactorRoots q r f :=
  letI : Algebra (Depth.RB (q+2*r)) A := (Collision.coeffHom (q+2*r) f).toRingHom.toAlgebra
  baseBlockAutomorphism q r A g

@[simp] theorem factorRootAutomorphism_root (q r : ℕ) (f : A[X]) (g : BlockGroup q r)
    (i : Fin q ⊕ Fin r) :
    factorRootAutomorphism q r f g (factorRoot q r f i) = factorRoot q r f (blockPermutation g i) := by
  let : Algebra (Depth.RB (q+2*r)) A := (Collision.coeffHom (q+2*r) f).toRingHom.toAlgebra
  exact baseBlockAutomorphism_root q r A g i

/-- Genuine signed permutation operators after the prescribed coefficient base change. -/
def factorSignedAction (q r : ℕ) (f : A[X]) :
    BlockGroup q r →* Module.End A (FactorRoots q r f) :=
  letI : Algebra (Depth.RB (q+2*r)) A := (Collision.coeffHom (q+2*r) f).toRingHom.toAlgebra
  (Module.End.baseChangeHom (Depth.RB (q+2*r)) A (LabelledWeightedRing q r)).toMonoidHom.comp
    (signedBlockAction q r)

theorem baseBlockSign_val (q r : ℕ) (S : Type) [CommRing S] [Algebra (Depth.RB (q+2*r)) S]
    (g : BlockGroup q r) :
    (baseBlockSign q r S g : S) = (((g.1.sign : ℤˣ) : ℤ) : S) := by
  simp [baseBlockSign,blockSign]

theorem factorSignedAction_apply (q r : ℕ) (f : A[X]) (g : BlockGroup q r)
    (x : FactorRoots q r f) :
    factorSignedAction q r f g x =
      ((((g.1.sign : ℤˣ) : ℤ) : A)) • factorRootAutomorphism q r f g x := by
  let : Algebra (Depth.RB (q+2*r)) A := (Collision.coeffHom (q+2*r) f).toRingHom.toAlgebra
  change (signedBlockOperator g).baseChange A x = _
  rw [signedBlock_baseChange_apply,baseBlockSign_val]
  rfl

/-- Arbitrary base change commutes with the actual signed invariant summand. -/
def factorSignedEquiv (q r : ℕ) (f : A[X]) :
    FactorSignedModule q r f ≃ₗ[A] FiberTransport.fixedVectors (factorSignedAction q r f) := by
  letI : Algebra (Depth.RB (q+2*r)) A := (Collision.coeffHom (q+2*r) f).toRingHom.toAlgebra
  exact signedInvariantBaseChangeEquiv q r A

def factorNormalization (q r : ℕ) : A :=
  algebraMap ℂ A ((Fintype.card (BlockGroup q r) : ℂ)⁻¹)

theorem factorNormalization_mul_card (q r : ℕ) :
    factorNormalization (A:=A) q r * (Fintype.card (BlockGroup q r) : A) = 1 := by
  have hn : (Fintype.card (BlockGroup q r) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold factorNormalization
  rw [← map_natCast (algebraMap ℂ A),← map_mul,inv_mul_cancel₀ hn,map_one]

end KhanSL2.Factorization.WeightedRootModel
