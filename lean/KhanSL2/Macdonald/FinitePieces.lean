module

public import KhanSL2.Macdonald.Grading
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-! Finite-dimensionality follows from concrete bounded supports and bounded
exponents. No finiteness hypothesis is imposed on the ambient mode algebra. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.Macdonald

theorem exponent_le_polynomialDegree (d : Exponent) (m : Mode) :
    d m ≤ polynomialDegree d := by
  by_cases hm : m ∈ d.support
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hm
  · simp [Finsupp.notMem_support_iff.mp hm, polynomialDegree]

theorem index_le_polynomialWeight {d : Exponent} {m : Mode} (hm : m ∈ d.support) :
    m.index ≤ polynomialWeight d := by
  have hn : 1 ≤ d m := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hm)
  exact (Nat.le_mul_of_pos_right m.index hn).trans
    (Finset.single_le_sum (f := fun i => i.index * d i) (fun _ _ => Nat.zero_le _) hm)

theorem index_succ_le_exteriorWeight {t : Finset Mode} {m : Mode} (hm : m ∈ t) :
    m.index + 1 ≤ exteriorWeight t := by
  unfold exteriorWeight
  exact Finset.single_le_sum (f := fun i : Mode => i.index + 1) (fun _ _ => Nat.zero_le _) hm

theorem exteriorDegree_le_weight (b : BasisIndex) : exteriorDegree b ≤ weight b := by
  have h : b.2.card ≤ exteriorWeight b.2 := by
    calc
      b.2.card = ∑ _m ∈ b.2, 1 := by simp
      _ ≤ exteriorWeight b.2 := Finset.sum_le_sum (fun m _ => Nat.le_add_left 1 m.index)
  exact h.trans (Nat.le_add_left _ _)

/-- Both bounds are necessary: weight alone does not bound the zero-mode powers. -/
def BoundedIndex (w s : ℕ) := {b : BasisIndex // weight b ≤ w ∧ symmetricDegree b ≤ s}

private theorem bounded_exponent (w s : ℕ) (b : BoundedIndex w s) (m : Mode) :
    b.val.1 m ≤ s :=
  (exponent_le_polynomialDegree b.val.1 m).trans b.property.2

private theorem bounded_polynomial_index (w s : ℕ) (b : BoundedIndex w s)
    {m : Mode} (hm : m ∈ b.val.1.support) : m.index ≤ w :=
  (index_le_polynomialWeight hm).trans ((Nat.le_add_right _ _).trans b.property.1)

private theorem bounded_exterior_index (w s : ℕ) (b : BoundedIndex w s)
    {m : Mode} (hm : m ∈ b.val.2) : m.index ≤ w :=
  (Nat.le_succ _).trans ((index_succ_le_exteriorWeight hm).trans
    ((Nat.le_add_left _ _).trans b.property.1))

private def boundedEncoding (w s : ℕ) (b : BoundedIndex w s) :
    ((Fin (w+1) × Fin 3) → Fin (s+1)) × Finset (Fin (w+1) × Fin 3) :=
  (fun i => ⟨b.val.1 ⟨i.1.val,i.2⟩, Nat.lt_succ_iff.mpr (bounded_exponent w s b _)⟩,
   Finset.univ.filter fun i => (⟨i.1.val,i.2⟩ : Mode) ∈ b.val.2)

private theorem boundedEncoding_injective (w s : ℕ) :
    Function.Injective (boundedEncoding w s) := by
  intro b c h
  apply Subtype.ext
  apply Prod.ext
  · apply Finsupp.ext
    intro m
    by_cases hm : m.index ≤ w
    · let i : Fin (w+1) × Fin 3 := (⟨m.index,Nat.lt_succ_iff.mpr hm⟩,m.color)
      have he := congrArg (fun q => (q.1 i).val) h
      simpa only [boundedEncoding, i] using he
    · have hb : b.val.1 m = 0 := by
        by_contra hn
        exact hm (bounded_polynomial_index w s b (Finsupp.mem_support_iff.mpr hn))
      have hc : c.val.1 m = 0 := by
        by_contra hn
        exact hm (bounded_polynomial_index w s c (Finsupp.mem_support_iff.mpr hn))
      exact hb.trans hc.symm
  · apply Finset.ext
    intro m
    by_cases hm : m.index ≤ w
    · let i : Fin (w+1) × Fin 3 := (⟨m.index,Nat.lt_succ_iff.mpr hm⟩,m.color)
      have he := Finset.ext_iff.mp (congrArg Prod.snd h) i
      simpa only [boundedEncoding, i, Finset.mem_filter, Finset.mem_univ, true_and] using he
    · have hb : m ∉ b.val.2 := fun hn => hm (bounded_exterior_index w s b hn)
      have hc : m ∉ c.val.2 := fun hn => hm (bounded_exterior_index w s c hn)
      simp only [hb,hc]

instance finite_boundedIndex (w s : ℕ) : Finite (BoundedIndex w s) :=
  Finite.of_injective (boundedEncoding w s) (boundedEncoding_injective w s)

/-- A finite window in weight and symmetric degree, allowing every exterior degree. -/
def finiteWindow (w s : ℕ) : Submodule ℂ W :=
  (Finsupp.supported ℂ ℂ {b : BasisIndex | weight b ≤ w ∧ symmetricDegree b ≤ s}).comap
    basis.repr.toLinearMap

instance finiteDimensional_finiteWindow (w s : ℕ) : FiniteDimensional ℂ (finiteWindow w s) := by
  let T : Set BasisIndex := {b | weight b ≤ w ∧ symmetricDegree b ≤ s}
  let : Finite T := finite_boundedIndex w s
  let f : finiteWindow w s →ₗ[ℂ] Finsupp.supported ℂ ℂ T :=
    { toFun := fun u => ⟨basis.repr u.val, u.property⟩
      map_add' := fun u v => by apply Subtype.ext; exact map_add basis.repr u.val v.val
      map_smul' := fun c u => by apply Subtype.ext; exact map_smul basis.repr c u.val }
  have hf : Function.Injective f := by
    intro u v h
    apply Subtype.ext
    exact basis.repr.injective (congrArg Subtype.val h)
  let e := Finsupp.supportedEquivFinsupp (M := ℂ) (R := ℂ) T
  exact FiniteDimensional.of_injective (e.toLinearMap.comp f) (e.injective.comp hf)

theorem piece_le_finiteWindow (w s k : ℕ) : piece w s k ≤ finiteWindow w s := by
  intro u hu
  change ∀ b ∈ (basis.repr u).support, weight b ≤ w ∧ symmetricDegree b ≤ s
  intro b hb
  obtain ⟨hw,hs,_⟩ := (mem_piece_iff u w s k).mp hu b hb
  exact ⟨hw.le,hs.le⟩

instance finiteDimensional_piece (w s k : ℕ) : FiniteDimensional ℂ (piece w s k) := by
  let f := Submodule.inclusion (piece_le_finiteWindow w s k)
  exact FiniteDimensional.of_injective (K := ℂ) (V := piece w s k)
    (V₂ := finiteWindow w s) f (Submodule.inclusion_injective (piece_le_finiteWindow w s k))

/-- Fixing weight and symmetric degree already gives a finite-dimensional total
cochain space, before choosing its exterior degree. -/
def weightDegreePiece (w s : ℕ) : Submodule ℂ W :=
  (Finsupp.supported ℂ ℂ {b : BasisIndex | weight b = w ∧ symmetricDegree b = s}).comap
    basis.repr.toLinearMap

instance finiteDimensional_weightDegreePiece (w s : ℕ) :
    FiniteDimensional ℂ (weightDegreePiece w s) := by
  have hle : weightDegreePiece w s ≤ finiteWindow w s := by
    intro u hu
    change ∀ b ∈ (basis.repr u).support, weight b = w ∧ symmetricDegree b = s at hu
    change ∀ b ∈ (basis.repr u).support, weight b ≤ w ∧ symmetricDegree b ≤ s
    intro b hb
    exact ⟨(hu b hb).1.le,(hu b hb).2.le⟩
  exact FiniteDimensional.of_injective (K := ℂ) (V := weightDegreePiece w s)
    (V₂ := finiteWindow w s) (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

theorem piece_eq_bot_of_weight_lt_degree {w s k : ℕ} (h : w < k) : piece w s k = ⊥ := by
  apply eq_bot_iff.mpr
  intro u hu
  change u = 0
  apply basis.repr.injective
  rw [map_zero]
  apply Finsupp.ext
  intro b
  change basis.repr u b = 0
  by_contra hn
  obtain ⟨hw,_,hk⟩ := (mem_piece_iff u w s k).mp hu b (Finsupp.mem_support_iff.mpr hn)
  have hb := exteriorDegree_le_weight b
  omega

end KhanSL2.Macdonald


