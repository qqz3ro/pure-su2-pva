module

public import KhanSL2.SymmetricFamily.RootScalarInvariants
public import KhanSL2.SymmetricFamily.LocalRootResidue

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The only symmetric root coefficient in the positive displacement ideal is
zero. This is the invariant-line input for strict top-weight drop. -/

noncomputable section
namespace KhanSL2.SymmetricFamily

/-- The original root permutations in the actual one-point root fibre. -/
def localRootPermutation (k : ℕ) (a : ℂ) (σ : Equiv.Perm (Fin k)) :
    LocalRootAlgebra k a ≃ₐ[ℂ] LocalRootAlgebra k a := by
  letI : Algebra (Depth.RB k) ℂ :=
    (Collision.coeffHom k ((Polynomial.X - Polynomial.C a)^k)).toRingHom.toAlgebra
  exact baseRootPermutation k ℂ σ

@[simp] theorem localRootPermutation_root (k : ℕ) (a : ℂ)
    (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    localRootPermutation k a σ (localRoot k a i) = localRoot k a (σ i) := by
  let : Algebra (Depth.RB k) ℂ :=
    (Collision.coeffHom k ((Polynomial.X - Polynomial.C a)^k)).toRingHom.toAlgebra
  exact baseRootPermutation_baseRoot k ℂ σ i

/-- All symmetric coefficients in the actual local root fibre are scalars. -/
theorem localRoot_fixed_isScalar (k : ℕ) (a : ℂ) (x : LocalRootAlgebra k a)
    (hx : ∀ σ : Equiv.Perm (Fin k), localRootPermutation k a σ x = x) :
    ∃ c : ℂ, algebraMap ℂ (LocalRootAlgebra k a) c = x := by
  let : Algebra (Depth.RB k) ℂ :=
    (Collision.coeffHom k ((Polynomial.X - Polynomial.C a)^k)).toRingHom.toAlgebra
  exact rootBase_fixed_isScalar k ℂ x hx

/-- Positive displacement degree contributes no symmetric root-invariant line. -/
theorem localRoot_fixed_mem_ideal_eq_zero (k : ℕ) (a : ℂ) (x : LocalRootAlgebra k a)
    (hx : ∀ σ : Equiv.Perm (Fin k), localRootPermutation k a σ x = x)
    (hI : x ∈ localRootIdeal k a) : x = 0 := by
  obtain ⟨c,hc⟩ := localRoot_fixed_isScalar k a x hx
  have he : localRootEvaluation k a x = 0 := localRootIdeal_le_ker k a hI
  rw [← hc, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at he
  rw [← hc, he, map_zero]

end KhanSL2.SymmetricFamily
