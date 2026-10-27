module

public import KhanSL2.Chains.RelativeHomology
public import KhanSL2.LieChains.Grading
public import Mathlib.Algebra.Polynomial.Derivative

@[expose] public section

/-!
# The trigrading of `Λ𝔩₊ ⊗ Λ(ε𝔩)` is intrinsic

`genPiece d` was defined by pulling back the monomial grading along the comparison
isomorphism `Phi`. This file shows that it is the joint eigenspace of three canonical
operators on the general chains, none of which refers to `Phi`:

* the form degree `p`: the derivation extension of `1` on `Λ𝔩₊`;
* the coefficient degree `B`: the derivation extension of `1` on `Λ(ε𝔩)`;
* the spin `S`: loop rotation `z d/dz`, extended as a derivation, with `ε` of spin one.

Precisely, `ξ ∈ genPiece (B + p, B, S)` iff `ξ` is an eigenvector of these with eigenvalues
`p`, `B` and `S` (`mem_genPiece_iff`).
-/

noncomputable section

open scoped TensorProduct
open Polynomial

namespace KhanSL2.Current

open LieChains

/-! ## Loop rotation -/

/-- Loop rotation `z d/dz` on `ℂ[z]`. -/
def euler : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ := LinearMap.mulLeft ℂ X ∘ₗ derivative

theorem euler_X_pow (n : ℕ) : euler (X ^ n : Polynomial ℂ) = (n : ℂ) • X ^ n := by
  rw [euler, LinearMap.comp_apply, LinearMap.mulLeft_apply, derivative_X_pow,
    Polynomial.smul_eq_C_mul]
  cases n with
  | zero => simp
  | succ n =>
    rw [Nat.add_sub_cancel, pow_succ]
    ring

/-- Loop rotation on `𝔩 = 𝔤[z]`. -/
def eulerCur : Module.End ℂ Cur := LinearMap.rTensor MatrixSL2 euler

theorem eulerCur_cur (n : ℕ) (a : Fin 3) : eulerCur (cur n a) = (n : ℂ) • cur n a := by
  rw [eulerCur, cur, LinearMap.rTensor_tmul, euler_X_pow, TensorProduct.smul_tmul']

theorem coeffZero_eulerCur (x : Cur) : coeffZero (eulerCur x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f m =>
    rw [eulerCur, LinearMap.rTensor_tmul, coeffZero_tmul, euler, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, coeff_X_mul_zero, zero_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-- Loop rotation on `𝔩₊`. -/
def eulerPlus : Module.End ℂ plus :=
  LinearMap.codRestrict (plus : Submodule ℂ Cur)
    (eulerCur ∘ₗ (plus : Submodule ℂ Cur).subtype) fun _ => coeffZero_eulerCur _

theorem eulerPlus_plusCur (j : ℕ) (a : Fin 3) :
    eulerPlus (plusCur j a) = ((j + 1 : ℕ) : ℂ) • plusCur j a := by
  apply Subtype.ext
  change eulerCur (cur (j + 1) a) = ((j + 1 : ℕ) : ℂ) • cur (j + 1) a
  rw [eulerCur_cur]

/-! ## The three grading operators -/

/-- The form degree: number of `𝔩₊` factors. -/
def formDegree : Module.End ℂ GenChains := lieDeriv 1 0

/-- The coefficient degree: exterior degree in `Λ(ε𝔩)`. -/
def coeffDegree : Module.End ℂ GenChains := lieDeriv 0 (derivExt 1)

/-- Spin on the coefficient generators `ε𝔩`: loop rotation shifted by the spin of `ε`. -/
def eulerCoeff : Module.End ℂ Cur := eulerCur + 1

/-- The spin: loop rotation `z d/dz` acting as a derivation, with `ε` of spin one. -/
def spin : Module.End ℂ GenChains := lieDeriv eulerPlus (derivExt eulerCoeff)

/-- The spin of an index `(j, a)`: `j + 1` both for `z^{j+1} t_a ∈ 𝔩₊` and for `ε z^j t_a`. -/
def idxSpin (q : Idx) : ℕ := (ofLex q).1 + 1

/-- Total spin of a set of indices. -/
def idxWeight (s : Finset Idx) : ℕ := ∑ q ∈ s, idxSpin q

theorem plusBasisLex_apply (q : Idx) : plusBasisLex q = plusCur (ofLex q).1 (ofLex q).2 := by
  rw [plusBasisLex, Module.Basis.reindex_apply]
  exact plusBasis_apply' _

theorem curBasisLex_apply (q : Idx) : curBasisLex q = cur (ofLex q).1 (ofLex q).2 := by
  rw [curBasisLex, Module.Basis.reindex_apply]
  exact curBasis_apply' _

theorem eulerPlus_basis (q : Idx) :
    eulerPlus (plusBasisLex q) = (idxSpin q : ℂ) • plusBasisLex q := by
  rw [plusBasisLex_apply, eulerPlus_plusCur]
  rfl

theorem eulerCoeff_basis (q : Idx) :
    eulerCoeff (curBasisLex q) = (idxSpin q : ℂ) • curBasisLex q := by
  rw [eulerCoeff, LinearMap.add_apply, Module.End.one_apply, curBasisLex_apply, eulerCur_cur, idxSpin]
  push_cast
  rw [add_smul, one_smul]

theorem genBasis_apply (s t : Finset Idx) :
    genBasis (s, t) = plusBasisLex.ExteriorAlgebra s ⊗ₜ curBasisLex.ExteriorAlgebra t := by
  rw [genBasis, Module.Basis.tensorProduct_apply]

theorem formDegree_genBasis (st : Finset Idx × Finset Idx) :
    formDegree (genBasis st) = (st.1.card : ℂ) • genBasis st := by
  obtain ⟨s, t⟩ := st
  rw [genBasis_apply, formDegree, lieDeriv_tmul, derivExt_one_basis, LinearMap.zero_apply,
    TensorProduct.tmul_zero, add_zero, TensorProduct.smul_tmul']

theorem coeffDegree_genBasis (st : Finset Idx × Finset Idx) :
    coeffDegree (genBasis st) = (st.2.card : ℂ) • genBasis st := by
  obtain ⟨s, t⟩ := st
  rw [genBasis_apply, coeffDegree, lieDeriv_tmul, derivExt_zero_apply, TensorProduct.zero_tmul,
    zero_add, derivExt_one_basis, TensorProduct.tmul_smul]

set_option maxHeartbeats 2000000 in
theorem spin_genBasis (st : Finset Idx × Finset Idx) :
    spin (genBasis st) = ((idxWeight st.1 + idxWeight st.2 : ℕ) : ℂ) • genBasis st := by
  obtain ⟨s, t⟩ := st
  have hw : ((idxWeight s + idxWeight t : ℕ) : ℂ) =
      (∑ q ∈ s, (idxSpin q : ℂ)) + ∑ q ∈ t, (idxSpin q : ℂ) := by
    push_cast [idxWeight]
    rfl
  have h1 : spin (plusBasisLex.ExteriorAlgebra s ⊗ₜ curBasisLex.ExteriorAlgebra t) =
      derivExt eulerPlus (plusBasisLex.ExteriorAlgebra s) ⊗ₜ curBasisLex.ExteriorAlgebra t +
        plusBasisLex.ExteriorAlgebra s ⊗ₜ derivExt eulerCoeff (curBasisLex.ExteriorAlgebra t) :=
    lieDeriv_tmul _ _ _ _
  rw [hw, add_smul, genBasis_apply, h1,
    derivExt_basis plusBasisLex eulerPlus (fun q => (idxSpin q : ℂ)) eulerPlus_basis,
    derivExt_basis curBasisLex eulerCoeff (fun q => (idxSpin q : ℂ)) eulerCoeff_basis,
    TensorProduct.smul_tmul', TensorProduct.tmul_smul]

/-! ## Coordinates of `Phi` -/

theorem chainBasis_apply (st : Finset Idx × Finset Idx) :
    chainBasis st = (splitSign st : ℂ) • Finsupp.single (splitEquiv st) 1 := by
  rw [chainBasis, Module.Basis.unitsSMul_apply, Module.Basis.reindex_apply, Equiv.symm_symm,
    Finsupp.coe_basisSingleOne, Units.smul_def]

/-- The monomial coefficients of `Phi ξ` are, up to sign, the tensor-basis coordinates of `ξ`. -/
theorem Phi_apply_splitEquiv (ξ : GenChains) (st : Finset Idx × Finset Idx) :
    Phi ξ (splitEquiv st) = (splitSign st : ℂ) * genBasis.repr ξ st := by
  have h : Finsupp.lapply (splitEquiv st) ∘ₗ Phi =
      (splitSign st : ℂ) • (Finsupp.lapply st ∘ₗ genBasis.repr.toLinearMap) := by
    apply genBasis.ext
    intro st'
    simp only [LinearMap.comp_apply, Phi_genBasis, chainBasis_apply, LinearMap.smul_apply,
      Finsupp.lapply_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.smul_apply,
      smul_eq_mul]
    by_cases hst : st' = st
    · subst hst
      simp
    · simp [Finsupp.single_apply, hst]
  exact congrArg (fun F => F ξ) h

theorem mem_genPiece_iff_repr (d : Degree) (ξ : GenChains) :
    ξ ∈ genPiece d ↔ ∀ st, genBasis.repr ξ st ≠ 0 → monomialDegree (splitEquiv st) = d := by
  rw [genPiece, Submodule.mem_comap, cochainPiece, Finsupp.mem_supported']
  refine (splitEquiv.forall_congr_right
    (q := fun m => m ∉ {s : ExteriorMonomial | monomialDegree s = d} → Phi ξ m = 0)).symm.trans ?_
  refine forall_congr' fun st => ?_
  simp only [Set.mem_setOf_eq]
  rw [Phi_apply_splitEquiv, mul_eq_zero, or_iff_right (Units.ne_zero _)]
  exact not_imp_comm

theorem monomialDegree_splitEquiv (s t : Finset Idx) :
    monomialDegree (splitEquiv (s, t)) =
      (((s.card + t.card : ℕ) : ℤ), (t.card : ℤ), ((idxWeight s + idxWeight t : ℕ) : ℤ)) := by
  change monomialDegree (s.map embC ∪ t.map embB) = _
  have hd := disjoint_split s t
  simp only [monomialDegree, Finset.card_union_eq_card_add_card.mpr hd, Finset.sum_union hd,
    Finset.card_map, Finset.sum_map]
  simp [embC, embB, mC, mB, Mode.bCount, Mode.weight, idxWeight, idxSpin]

set_option maxHeartbeats 2000000 in
/-- **The trigrading is intrinsic.** The degree-`(B + p, B, S)` piece of the general chains is
the joint eigenspace of form degree `p`, coefficient degree `B` and spin `S`. -/
theorem mem_genPiece_iff (p B : ℕ) (S : ℤ) (ξ : GenChains) :
    ξ ∈ genPiece (((B + p : ℕ) : ℤ), (B : ℤ), S) ↔
      formDegree ξ = (p : ℂ) • ξ ∧ coeffDegree ξ = (B : ℂ) • ξ ∧ spin ξ = (S : ℂ) • ξ := by
  rw [mem_genPiece_iff_repr,
    genBasis.apply_eq_smul_iff_of_diagonal formDegree _ formDegree_genBasis,
    genBasis.apply_eq_smul_iff_of_diagonal coeffDegree _ coeffDegree_genBasis,
    genBasis.apply_eq_smul_iff_of_diagonal spin _ spin_genBasis, ← forall_and, ← forall_and]
  refine forall_congr' fun st => ?_
  rw [← imp_and, ← imp_and]
  refine imp_congr_right fun _ => ?_
  obtain ⟨s, t⟩ := st
  rw [monomialDegree_splitEquiv]
  simp only [Prod.mk.injEq]
  have e1 : ((s.card : ℂ) = p) ↔ s.card = p := Nat.cast_inj
  have e2 : ((t.card : ℂ) = B) ↔ t.card = B := Nat.cast_inj
  have e3 : (((idxWeight s + idxWeight t : ℕ) : ℂ) = (S : ℂ)) ↔
      ((idxWeight s + idxWeight t : ℕ) : ℤ) = S := by
    rw [← Int.cast_natCast, Int.cast_inj]
  rw [e1, e2, e3]
  omega

end KhanSL2.Current
