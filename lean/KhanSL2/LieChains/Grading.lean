module

public import KhanSL2.LieChains.DerivExt
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

@[expose] public section

/-!
# Diagonal derivations on exterior algebras

If `D` is diagonal in a basis `b` of `L`, with `D (b i) = μ i • b i`, then the derivation
extension `derivExt D` is diagonal in the monomial basis `b.ExteriorAlgebra` of `ΛL`,
with eigenvalue `∑ i ∈ s, μ i` on `b.ExteriorAlgebra s`. In particular `derivExt 1` is
the form-degree operator.

We also record the elementary fact that, for an operator diagonal in a basis, the
`c`-eigenvectors are exactly the vectors whose basis coordinates are supported on the
indices of eigenvalue `c`.
-/

noncomputable section

namespace KhanSL2.LieChains

open ExteriorAlgebra

variable {k L : Type*} [CommRing k] [AddCommGroup L] [Module k L]

theorem derivExt_list_prod {I : Type*} (v : I → L) (D : Module.End k L) (μ : I → k)
    (hD : ∀ i, D (v i) = μ i • v i) (l : List I) :
    derivExt D (l.map fun i => ι k (v i)).prod =
      (l.map μ).sum • (l.map fun i => ι k (v i)).prod := by
  induction l with
  | nil => simp [derivExt_one]
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [derivExt_ι_mul, hD, ih, map_smul, smul_mul_assoc, mul_smul_comm, add_smul]

theorem sum_univ_map_orderEmb {I : Type*} [LinearOrder I] {n : ℕ} (μ : I → k)
    (u : Set.powersetCard I n) :
    ∑ j : Fin n, μ (Set.powersetCard.ofFinEmbEquiv.symm u j) = ∑ i ∈ u.val, μ i := by
  have h : Finset.univ.map (Set.powersetCard.ofFinEmbEquiv.symm u).toEmbedding = u.val := by
    ext p
    simp only [Finset.mem_map, Finset.mem_univ, true_and, RelEmbedding.coe_toEmbedding]
    exact Set.mem_range.symm.trans (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem u p)
  rw [← h, Finset.sum_map]
  rfl

/-- A derivation extension of a diagonal operator is diagonal on monomials. -/
theorem derivExt_basis {I : Type*} [LinearOrder I] (b : Module.Basis I k L)
    (D : Module.End k L) (μ : I → k) (hD : ∀ i, D (b i) = μ i • b i) (s : Finset I) :
    derivExt D (b.ExteriorAlgebra s) = (∑ i ∈ s, μ i) • b.ExteriorAlgebra s := by
  rw [ExteriorAlgebra.basis_apply_ofCard b (rfl : s.card = s.card)]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply, Function.comp_def]
  have hl := derivExt_list_prod (k := k) b D μ hD
    (List.ofFn fun j => Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard
      (rfl : s.card = s.card)) j)
  simp only [List.map_ofFn, Function.comp_def] at hl
  rw [hl, List.sum_ofFn, sum_univ_map_orderEmb]
  rfl

/-- The form-degree operator. -/
theorem derivExt_one_basis {I : Type*} [LinearOrder I] (b : Module.Basis I k L)
    (s : Finset I) :
    derivExt (1 : Module.End k L) (b.ExteriorAlgebra s) = (s.card : k) • b.ExteriorAlgebra s := by
  rw [derivExt_basis b 1 (fun _ => 1) (fun i => by simp), Finset.sum_const, nsmul_eq_mul,
    mul_one]

theorem derivExt_zero_apply (x : ExteriorAlgebra k L) : derivExt (0 : Module.End k L) x = 0 := by
  have h := derivExt_smul (0 : k) (1 : Module.End k L)
  rw [zero_smul] at h
  rw [h, zero_smul]

end KhanSL2.LieChains

namespace Module.Basis

variable {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- Coordinates of `T v` for an operator diagonal in the basis `b`. -/
theorem repr_apply_of_diagonal (b : Module.Basis ι k V) (T : Module.End k V) (μ : ι → k)
    (hT : ∀ i, T (b i) = μ i • b i) (v : V) (i : ι) :
    b.repr (T v) i = μ i * b.repr v i := by
  have h : (Finsupp.lapply i ∘ₗ b.repr.toLinearMap ∘ₗ T) =
      μ i • (Finsupp.lapply i ∘ₗ b.repr.toLinearMap) := by
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hT, map_smul, Module.Basis.repr_self,
      Finsupp.lapply_apply, LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul]
    by_cases hji : j = i
    · rw [hji]
    · rw [Finsupp.single_eq_of_ne (Ne.symm hji), mul_zero, mul_zero]
  exact congrArg (fun F => F v) h

/-- For an operator diagonal in a basis, the `c`-eigenvectors are the vectors supported on
indices of eigenvalue `c`. -/
theorem apply_eq_smul_iff_of_diagonal (b : Module.Basis ι k V) (T : Module.End k V)
    (μ : ι → k) (hT : ∀ i, T (b i) = μ i • b i) (c : k) (v : V) :
    T v = c • v ↔ ∀ i, b.repr v i ≠ 0 → μ i = c := by
  rw [← b.repr.injective.eq_iff, Finsupp.ext_iff]
  simp only [repr_apply_of_diagonal b T μ hT, map_smul, Finsupp.smul_apply, smul_eq_mul]
  refine forall_congr' fun i => ?_
  constructor
  · intro h hv
    exact mul_right_cancel₀ hv h
  · intro h
    by_cases hv : b.repr v i = 0
    · rw [hv, mul_zero, mul_zero]
    · rw [h hv]

end Module.Basis
