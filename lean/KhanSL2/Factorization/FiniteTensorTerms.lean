module

public import KhanSL2.Factorization.FiniteBGGChart
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.DirectSum.Finite

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex MonoidalCategory
open scoped TensorProduct DirectSum
namespace KhanSL2.Factorization

variable {A : Type} [CommRing A]

/-- The actual finite set of bidegrees contributing to a nonnegative tensor degree. -/
def TensorDegreeIndex (n : ℕ) := {pq : ℕ × ℕ // pq.1 + pq.2 = n}

instance (n : ℕ) : Finite (TensorDegreeIndex n) := by
  let f : TensorDegreeIndex n → Fin (n+1) := fun i => ⟨i.val.1,by have := i.property; omega⟩
  apply Finite.of_injective f
  intro i j h
  have hp : i.val.1=j.val.1 := congrArg Fin.val h
  apply Subtype.ext
  apply Prod.ext hp
  have hi := i.property
  have hj := j.property
  omega

/-- The categorical tensor degree is the literal direct sum over its finitely
many nonnegative bidegrees. -/
def tensorDegreeDirectSumEquiv (C D : ChainComplex (ModuleCat A) ℕ) (n : ℕ) :
    (HomologicalComplex.tensorObj C D).X n ≃ₗ[A]
      ⨁ i : TensorDegreeIndex n, C.X i.val.1 ⊗[A] D.X i.val.2 := by
  classical
  exact (ModuleCat.coprodIsoDirectSum
    (fun i : TensorDegreeIndex n => ModuleCat.of A (C.X i.val.1 ⊗[A] D.X i.val.2))).toLinearEquiv

/-- Tensoring two complexes with finite terms again has finite terms. -/
theorem tensorComplex_term_finite (C D : ChainComplex (ModuleCat A) ℕ)
    [∀j, Module.Finite A (C.X j)] [∀j, Module.Finite A (D.X j)] (n : ℕ) :
    Module.Finite A ((HomologicalComplex.tensorObj C D).X n) := by
  let e := tensorDegreeDirectSumEquiv C D n
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

/-- Tensoring termwise projective complexes remains termwise projective. -/
theorem tensorComplex_term_projective (C D : ChainComplex (ModuleCat A) ℕ)
    [∀j, Module.Projective A (C.X j)] [∀j, Module.Projective A (D.X j)] (n : ℕ) :
    Module.Projective A ((HomologicalComplex.tensorObj C D).X n) := by
  let e := tensorDegreeDirectSumEquiv C D n
  exact Module.Projective.of_equiv e.symm

end KhanSL2.Factorization

