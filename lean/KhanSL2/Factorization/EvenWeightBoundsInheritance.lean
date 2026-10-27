module

public import KhanSL2.Factorization.EvenWeightBounds
public import Mathlib.Algebra.Lie.Quotient

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
namespace KhanSL2.Factorization.EvenWeightBounds

variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- A genuine intertwiner commutes with every polynomial in the operators. -/
theorem aeval_intertwines (T : Module.End ℂ V) (U : Module.End ℂ W) (f : V →ₗ[ℂ] W)
    (hf : ∀ v, f (T v) = U (f v)) (p : Polynomial ℂ) (v : V) :
    f (aeval T p v) = aeval U p (f v) := by
  have hpow (n : ℕ) : f ((T^n) v) = (U^n) (f v) := by
    induction n with
    | zero => rfl
    | succ n hn =>
      rw [pow_succ',pow_succ',Module.End.mul_apply,Module.End.mul_apply,hf,hn]
  rw [aeval_endomorphism,aeval_endomorphism]
  simp only [Polynomial.sum,map_sum,map_smul,hpow]

theorem annihilator_of_injective (T : Module.End ℂ V) (U : Module.End ℂ W)
    (f : V →ₗ[ℂ] W) (hf : Function.Injective f)
    (hcomm : ∀ v, f (T v) = U (f v)) (p : Polynomial ℂ) (hp : aeval U p = 0) :
    aeval T p = 0 := by
  ext v
  apply hf
  rw [aeval_intertwines T U f hcomm,hp]
  simp

theorem annihilator_of_surjective (T : Module.End ℂ V) (U : Module.End ℂ W)
    (f : V →ₗ[ℂ] W) (hf : Function.Surjective f)
    (hcomm : ∀ v, f (T v) = U (f v)) (p : Polynomial ℂ) (hp : aeval T p = 0) :
    aeval U p = 0 := by
  ext w
  obtain ⟨v,rfl⟩ := hf w
  rw [← aeval_intertwines T U f hcomm,hp]
  simp

variable [LieRingModule BGG.G V] [LieModule ℂ BGG.G V]
  [LieRingModule BGG.G W] [LieModule ℂ BGG.G W]

/-- Polynomial Cartan bounds inherit through actual injective G-module maps. -/
theorem cartan_annihilator_of_injective (f : V →ₗ⁅ℂ,BGG.G⁆ W)
    (hf : Function.Injective f) (p : Polynomial ℂ) (hp : aeval (cartan W) p = 0) :
    aeval (cartan V) p = 0 :=
  annihilator_of_injective (cartan V) (cartan W) f.toLinearMap hf
    (fun v => f.map_lie MatrixSL2.h v) p hp

/-- Polynomial Cartan bounds inherit through actual surjective G-module maps. -/
theorem cartan_annihilator_of_surjective (f : V →ₗ⁅ℂ,BGG.G⁆ W)
    (hf : Function.Surjective f) (p : Polynomial ℂ) (hp : aeval (cartan V) p = 0) :
    aeval (cartan W) p = 0 :=
  annihilator_of_surjective (cartan V) (cartan W) f.toLinearMap hf
    (fun v => f.map_lie MatrixSL2.h v) p hp

/-- The annihilator statement for any invariant submodule of the actual module. -/
theorem cartan_annihilator_submodule (N : LieSubmodule ℂ BGG.G V)
    (p : Polynomial ℂ) (hp : aeval (cartan V) p = 0) :
    aeval (cartan N) p = 0 :=
  cartan_annihilator_of_injective N.incl Subtype.val_injective p hp

/-- The annihilator statement for the actual quotient by an invariant submodule. -/
theorem cartan_annihilator_quotient (N : LieSubmodule ℂ BGG.G V)
    (p : Polynomial ℂ) (hp : aeval (cartan V) p = 0) :
    aeval (cartan (V ⧸ N)) p = 0 :=
  cartan_annihilator_of_surjective (LieSubmodule.Quotient.mk' N)
    (LieSubmodule.Quotient.surjective_mk' N) p hp

end KhanSL2.Factorization.EvenWeightBounds