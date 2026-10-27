module

public import KhanSL2.SymmetricFamily.LocalRootInvariants
public import KhanSL2.SymmetricFamily.LocalRootFiltration
public import KhanSL2.SymmetricFamily.ColorTopLine

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Strict top-weight drop in the positive displacement part of the actual
symmetric root/color fibre. No regular-representation statement is used. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG

/-- Honest simultaneous permutations in the actual one-point root/color fibre. -/
def localRootColorPermute (k : ℕ) (a : ℂ) (σ : Equiv.Perm (Fin k)) :
    Module.End ℂ (LocalRootColors k a) :=
  TensorProduct.map (localRootPermutation k a σ).toLinearMap (colorPermute σ.symm)

/-- Each literal color coordinate retains membership in the displacement ideal power. -/
theorem localColorCoordinate_mem (k : ℕ) (a : ℂ) (d : ℕ) (x : LocalRootColors k a)
    (hx : x ∈ localRootColorFiltration k a d) (c : Fin k → Fin 3) :
    colorCoordinates k (LocalRootAlgebra k a) x c ∈ localRootIdeal k a ^ d := by
  change x ∈ idealTensorSubmodule (Color k) (localRootIdeal k a ^ d) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q,hq,v,rfl⟩ := hy
    rw [colorCoordinates_tmul, Algebra.smul_def]
    exact (localRootIdeal k a ^ d).mul_mem_left _ hq
  | zero => simp
  | add x y _ _ hx hy =>
    simpa only [map_add, Pi.add_apply] using (localRootIdeal k a ^ d).add_mem hx hy
  | smul z x _ hx =>
    rw [map_smul, Pi.smul_apply, Algebra.smul_def]
    exact (localRootIdeal k a ^ d).mul_mem_left _ hx

/-- A top eigenvector fixed by slots has a symmetric root coefficient. -/
theorem localRootColor_top_coefficient_fixed (k : ℕ) (a : ℂ)
    (x : LocalRootColors k a)
    (hperm : ∀ σ : Equiv.Perm (Fin k), localRootColorPermute k a σ x = x)
    (q : LocalRootAlgebra k a)
    (hq : x = q ⊗ₜ[ℂ] Pi.basisFun ℂ (Fin k → Fin 3) (fun _ => 0)) :
    ∀ σ : Equiv.Perm (Fin k), localRootPermutation k a σ q = q := by
  intro σ
  have h := congrArg (fun y => colorCoordinates k (LocalRootAlgebra k a) y (fun _ => 0))
    (hperm σ)
  rw [hq] at h
  simpa only [localRootColorPermute, TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply,
    colorPermute_basis, Function.comp_def, colorCoordinates_basis_tmul, ite_true] using h

/-- The actual positive displacement invariant subspace has no top Cartan eigenvector. -/
theorem localRootColor_positive_top_eq_zero (k : ℕ) (a : ℂ) (x : LocalRootColors k a)
    (hperm : ∀ σ : Equiv.Perm (Fin k), localRootColorPermute k a σ x = x)
    (hI : x ∈ localRootColorFiltration k a 1)
    (hcartan : LinearMap.lTensor (LocalRootAlgebra k a)
      (colorDeriv k (LieAlgebra.ad ℂ BGG.G MatrixSL2.h)) x = (2*(k : ℂ)) • x) :
    x = 0 := by
  obtain ⟨q,hq⟩ := exists_root_tmul_top_of_cartan k (LocalRootAlgebra k a) x hcartan
  have hsym := localRootColor_top_coefficient_fixed k a x hperm q hq
  have hqi := localColorCoordinate_mem k a 1 x hI (fun _ => 0)
  rw [hq, colorCoordinates_basis_tmul, if_pos rfl, pow_one] at hqi
  have hz := localRoot_fixed_mem_ideal_eq_zero k a q hsym hqi
  rw [hq, hz, TensorProduct.zero_tmul]

end KhanSL2.SymmetricFamily
