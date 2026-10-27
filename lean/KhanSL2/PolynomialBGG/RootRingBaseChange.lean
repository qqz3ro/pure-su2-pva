module

public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section

/-! # Polynomial base change preserves module freeness -/

noncomputable section
namespace KhanSL2.PolynomialBGG

attribute [local instance] Polynomial.algebra

/-- If S is free over R, then S[T] is free over R[T] through coefficient extension. -/
theorem polynomial_free_of_free (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Module.Free R S] :
    Module.Free (Polynomial R) (Polynomial S) :=
  Module.Free.of_equiv (Algebra.IsPushout.equiv R (Polynomial R) S (Polynomial S)).toLinearEquiv

end KhanSL2.PolynomialBGG
