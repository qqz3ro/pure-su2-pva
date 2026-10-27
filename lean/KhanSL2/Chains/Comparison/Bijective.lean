module

public import KhanSL2.Chains.Comparison.Setup
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Data.List.Sort

@[expose] public section

/-!
# `Phi` is a linear isomorphism

`Phi` sends the tensor product of Mathlib's exterior-algebra bases of `Λ𝔩₊` and
`Λ(ε𝔩)` to plus or minus the monomial basis of finite chains, through the bijection
`(s, t) ↦ c(s) ∪ b(t)`.
-/

noncomputable section

open scoped TensorProduct

namespace KhanSL2.Current

open FiniteExterior

/-- Index set, ordered lexicographically. -/
abbrev Idx := Lex (ℕ × Fin 3)

/-- `(j, a) ↦ c_j^a`. -/
def mC (p : Idx) : Mode := Mode.c (ofLex p).1 (ofLex p).2

/-- `(j, a) ↦ b_j^a`. -/
def mB (p : Idx) : Mode := Mode.b (ofLex p).1 (ofLex p).2

theorem lex_code_lt {p q : Idx} (h : p < q) :
    6 * (ofLex p).1 + (ofLex p).2.val < 6 * (ofLex q).1 + (ofLex q).2.val := by
  have ha := (ofLex p).2.isLt
  have hb := (ofLex q).2.isLt
  rcases Prod.Lex.lt_iff.mp h with h1 | ⟨h1, h2⟩
  · omega
  · rw [Fin.lt_iff_val_lt_val] at h2
    omega

theorem mC_code_lt {p q : Idx} (h : p < q) : (mC p).code < (mC q).code := by
  have := lex_code_lt h
  simp only [mC, Mode.code]
  omega

theorem mB_code_lt {p q : Idx} (h : p < q) : (mB p).code < (mB q).code := by
  have := lex_code_lt h
  simp only [mB, Mode.code]
  omega

theorem mC_injective : Function.Injective mC := by
  intro p q h
  rcases lt_trichotomy p q with hpq | rfl | hpq
  · exact absurd (congrArg Mode.code h) (ne_of_lt (mC_code_lt hpq))
  · rfl
  · exact absurd (congrArg Mode.code h).symm (ne_of_lt (mC_code_lt hpq))

theorem mB_injective : Function.Injective mB := by
  intro p q h
  rcases lt_trichotomy p q with hpq | rfl | hpq
  · exact absurd (congrArg Mode.code h) (ne_of_lt (mB_code_lt hpq))
  · rfl
  · exact absurd (congrArg Mode.code h).symm (ne_of_lt (mB_code_lt hpq))

/-- `c`-generators. -/
abbrev embC : Idx ↪ Mode := ⟨mC, mC_injective⟩

/-- `b`-generators. -/
abbrev embB : Idx ↪ Mode := ⟨mB, mB_injective⟩

/-! ## Products of sorted generators -/

theorem list_prod_generator (l : List Mode) (hl : l.Pairwise (fun x y => x.code < y.code)) :
    (l.map generator).prod = Finsupp.single l.toFinset 1 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.pairwise_cons] at hl
    rw [List.map_cons, List.prod_cons, ih hl.2, List.toFinset_cons]
    change FiniteExterior.wedge GeneratorOrder.code (Finsupp.single {x} 1)
      (Finsupp.single l.toFinset 1) = _
    rw [FiniteExterior.wedge_single, one_mul, one_smul, FiniteExterior.monomialWedge]
    have hx : x ∉ l.toFinset := by
      intro hx
      exact lt_irrefl _ (hl.1 x (List.mem_toFinset.mp hx))
    rw [if_pos (Finset.disjoint_singleton_left.mpr hx), Finset.singleton_union]
    congr 1
    have h0 : FiniteExterior.inversionCount GeneratorOrder.code {x} l.toFinset = 0 := by
      rw [FiniteExterior.inversionCount, Finset.sum_singleton, Finset.card_eq_zero,
        Finset.filter_eq_empty_iff]
      intro y hy
      exact not_lt.mpr (hl.1 y (List.mem_toFinset.mp hy)).le
    rw [h0, pow_zero]

/-! ## Images of basis vectors -/

/-- The basis of `𝔩₊` indexed lexicographically. -/
def plusBasisLex : Module.Basis Idx ℂ plus := plusBasis.reindex toLex

/-- The basis of `𝔩` indexed lexicographically. -/
def curBasisLex : Module.Basis Idx ℂ Cur := curBasis.reindex toLex

theorem plusBasis_apply' (q : ℕ × Fin 3) : plusBasis q = plusCur q.1 q.2 := plusBasis_apply q.1 q.2

theorem phiC_plusBasisLex (p : Idx) : phiC (plusBasisLex p) = generator (mC p) := by
  simp [plusBasisLex, mC, plusBasis_apply']

theorem phiB_curBasisLex (p : Idx) : phiB (curBasisLex p) = generator (mB p) := by
  simp [curBasisLex, mB, curBasis_apply']

theorem prod_ofFn_generator_C {n : ℕ} (e : Fin n ↪o Idx) :
    (List.ofFn fun i => generator (mC (e i))).prod =
      Finsupp.single ((Finset.univ.map e.toEmbedding).map ⟨mC, mC_injective⟩) 1 := by
  have h := list_prod_generator (List.ofFn fun i => mC (e i)) (by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact mC_code_lt (e.strictMono hij))
  rw [List.map_ofFn] at h
  rw [show (generator ∘ fun i => mC (e i)) = fun i => generator (mC (e i)) from rfl] at h
  rw [h]
  congr 1
  ext m
  simp

theorem prod_ofFn_generator_B {n : ℕ} (e : Fin n ↪o Idx) :
    (List.ofFn fun i => generator (mB (e i))).prod =
      Finsupp.single ((Finset.univ.map e.toEmbedding).map ⟨mB, mB_injective⟩) 1 := by
  have h := list_prod_generator (List.ofFn fun i => mB (e i)) (by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact mB_code_lt (e.strictMono hij))
  rw [List.map_ofFn] at h
  rw [show (generator ∘ fun i => mB (e i)) = fun i => generator (mB (e i)) from rfl] at h
  rw [h]
  congr 1
  ext m
  simp

theorem map_univ_ofFinEmbEquiv_symm {n : ℕ} (u : Set.powersetCard Idx n) :
    Finset.univ.map (Set.powersetCard.ofFinEmbEquiv.symm u).toEmbedding = u.val := by
  ext p
  simp only [Finset.mem_map, Finset.mem_univ, true_and, RelEmbedding.coe_toEmbedding]
  exact Set.mem_range.symm.trans (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem u p)

theorem PhiC_basis (s : Finset Idx) :
    PhiC (plusBasisLex.ExteriorAlgebra s) = Finsupp.single (s.map ⟨mC, mC_injective⟩) 1 := by
  rw [ExteriorAlgebra.basis_apply_ofCard plusBasisLex (rfl : s.card = s.card)]
  simp only [ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn, Function.comp_def, PhiC_ι,
    phiC_plusBasisLex]
  rw [prod_ofFn_generator_C, map_univ_ofFinEmbEquiv_symm]
  rfl

theorem PhiB_basis (t : Finset Idx) :
    PhiB (curBasisLex.ExteriorAlgebra t) = Finsupp.single (t.map ⟨mB, mB_injective⟩) 1 := by
  rw [ExteriorAlgebra.basis_apply_ofCard curBasisLex (rfl : t.card = t.card)]
  simp only [ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn, Function.comp_def, PhiB_ι,
    phiB_curBasisLex]
  rw [prod_ofFn_generator_B, map_univ_ofFinEmbEquiv_symm]
  rfl

/-! ## The index bijection -/

theorem mC_ne_mB (p q : Idx) : mC p ≠ mB q := by simp [mC, mB]

theorem mC_toLex (j : ℕ) (a : Fin 3) : mC (toLex (j, a)) = Mode.c j a := rfl

theorem mB_toLex (j : ℕ) (a : Fin 3) : mB (toLex (j, a)) = Mode.b j a := rfl

/-- `(s, t) ↦ c(s) ∪ b(t)`. -/
def splitEquiv : (Finset Idx × Finset Idx) ≃ Finset Mode where
  toFun st := st.1.map embC ∪ st.2.map embB
  invFun S := (S.preimage mC mC_injective.injOn, S.preimage mB mB_injective.injOn)
  left_inv st := by
    obtain ⟨s, t⟩ := st
    ext p
    · simp only [Finset.mem_preimage, Finset.mem_union, Finset.mem_map,
        Function.Embedding.coeFn_mk, mC_injective.eq_iff, exists_eq_right]
      simp [(mC_ne_mB _ _).symm]
    · simp only [Finset.mem_preimage, Finset.mem_union, Finset.mem_map,
        Function.Embedding.coeFn_mk, mB_injective.eq_iff, exists_eq_right]
      simp [mC_ne_mB]
  right_inv S := by
    ext m
    simp only [Finset.mem_union, Finset.mem_map, Finset.mem_preimage, embC, embB,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) <;> exact hp
    · intro hm
      cases m with
      | c j a => exact Or.inl ⟨toLex (j, a), hm, rfl⟩
      | b j a => exact Or.inr ⟨toLex (j, a), hm, rfl⟩

theorem disjoint_split (s t : Finset Idx) : Disjoint (s.map embC) (t.map embB) := by
  rw [Finset.disjoint_left]
  rintro m hm hm'
  obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hm
  obtain ⟨q, _, hq⟩ := Finset.mem_map.mp hm'
  exact mC_ne_mB p q hq.symm

/-- The sign comparing the two orderings. -/
def splitSign (st : Finset Idx × Finset Idx) : ℂˣ :=
  (-1) ^ FiniteExterior.inversionCount GeneratorOrder.code (st.1.map embC) (st.2.map embB)

/-! ## `Phi` maps a basis to a basis -/

/-- The tensor basis of `Λ𝔩₊ ⊗ Λ(ε𝔩)`. -/
def genBasis : Module.Basis (Finset Idx × Finset Idx) ℂ GenChains :=
  plusBasisLex.ExteriorAlgebra.tensorProduct curBasisLex.ExteriorAlgebra

/-- The signed monomial basis of chains, indexed through `splitEquiv`. -/
def chainBasis : Module.Basis (Finset Idx × Finset Idx) ℂ Chain :=
  ((Finsupp.basisSingleOne : Module.Basis (Finset Mode) ℂ Chain).reindex
    splitEquiv.symm).unitsSMul splitSign

theorem Phi_genBasis (st : Finset Idx × Finset Idx) : Phi (genBasis st) = chainBasis st := by
  obtain ⟨s, t⟩ := st
  rw [genBasis, Module.Basis.tensorProduct_apply, Phi_tmul, PhiC_basis, PhiB_basis,
    chainBasis, Module.Basis.unitsSMul_apply, Module.Basis.reindex_apply, Equiv.symm_symm,
    Finsupp.coe_basisSingleOne]
  change FiniteExterior.wedge GeneratorOrder.code _ _ = _
  rw [FiniteExterior.wedge_single, one_mul, one_smul, FiniteExterior.monomialWedge,
    if_pos (disjoint_split s t), splitSign, Units.smul_def, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one, Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

/-- **`Phi` is a linear isomorphism.** -/
def PhiEquiv : GenChains ≃ₗ[ℂ] Chain := genBasis.equiv chainBasis (Equiv.refl _)

theorem PhiEquiv_toLinearMap : PhiEquiv.toLinearMap = Phi := by
  apply genBasis.ext
  intro st
  rw [LinearEquiv.coe_coe, PhiEquiv, Module.Basis.equiv_apply, Equiv.refl_apply, Phi_genBasis]

theorem PhiEquiv_apply (ξ : GenChains) : PhiEquiv ξ = Phi ξ :=
  congrArg (fun F : GenChains →ₗ[ℂ] Chain => F ξ) PhiEquiv_toLinearMap

theorem Phi_bijective : Function.Bijective Phi := by
  rw [← PhiEquiv_toLinearMap]
  exact PhiEquiv.bijective

end KhanSL2.Current
