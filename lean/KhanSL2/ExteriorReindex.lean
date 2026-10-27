module

public import KhanSL2.ExteriorRing
public import KhanSL2.ExteriorDerivation

@[expose] public section

/-! Injective reindexing of ordered exterior generators. -/

noncomputable section

namespace KhanSL2.FiniteExterior

variable {α β : Type*}

def reindex (f : α ↪ β) : Exterior α →ₗ[ℂ] Exterior β :=
  Finsupp.lmapDomain ℂ ℂ (Finset.map f)

@[simp] theorem reindex_single (f : α ↪ β) (s : Finset α) (r : ℂ) :
    reindex f (Finsupp.single s r) = Finsupp.single (s.map f) r := by
  simp [reindex]

@[simp] theorem reindex_monomial (f : α ↪ β) (s : Finset α) :
    reindex f (monomial s) = monomial (s.map f) := by simp [monomial]

@[simp] theorem reindex_generator (f : α ↪ β) (a : α) :
    reindex f (generator a) = generator (f a) := by simp [generator]

@[simp] theorem reindex_one (f : α ↪ β) :
    reindex f (monomial ∅) = monomial ∅ := by simp

theorem reindex_injective (f : α ↪ β) : Function.Injective (reindex f) :=
  Finsupp.mapDomain_injective (Finset.map_injective f)

theorem inversionCount_map (codeA : α → ℕ) (codeB : β → ℕ) (f : α ↪ β)
    (hf : ∀a b, codeB (f a) < codeB (f b) ↔ codeA a < codeA b)
    (s t : Finset α) :
    inversionCount codeB (s.map f) (t.map f) = inversionCount codeA s t := by
  simp only [inversionCount, Finset.sum_map, Finset.filter_map, Finset.card_map,
    Function.comp_def]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply Finset.filter_congr
  intro b _
  exact hf b a

theorem position_map (codeA : α → ℕ) (codeB : β → ℕ) (f : α ↪ β)
    (hf : ∀a b, codeB (f a) < codeB (f b) ↔ codeA a < codeA b)
    (a : α) (s : Finset α) :
    position codeB (f a) (s.map f) = position codeA a s := by
  simp only [position, Finset.filter_map, Finset.card_map, Function.comp_def]
  congr 1
  apply Finset.filter_congr
  intro b _
  exact hf b a

variable [DecidableEq α] [DecidableEq β]

theorem reindex_monomialWedge (codeA : α → ℕ) (codeB : β → ℕ) (f : α ↪ β)
    (hf : ∀a b, codeB (f a) < codeB (f b) ↔ codeA a < codeA b)
    (s t : Finset α) :
    reindex f (monomialWedge codeA s t) =
      monomialWedge codeB (s.map f) (t.map f) := by
  by_cases h : Disjoint s t
  · simp [monomialWedge, h, Finset.map_union, inversionCount_map codeA codeB f hf]
  · simp [monomialWedge, h]

theorem reindex_wedge (codeA : α → ℕ) (codeB : β → ℕ) (f : α ↪ β)
    (hf : ∀a b, codeB (f a) < codeB (f b) ↔ codeA a < codeA b)
    (u v : Exterior α) :
    reindex f (wedge codeA u v) = wedge codeB (reindex f u) (reindex f v) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u w hu hw => simp only [wedge_add_left, map_add, hu, hw]
  | single s r =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp only [wedge_add_right, map_add, hv, hw]
    | single t q =>
      simp only [reindex_single, wedge_single, map_smul,
        reindex_monomialWedge codeA codeB f hf]

omit [DecidableEq α] [DecidableEq β] in
theorem reindex_parity (f : α ↪ β) (u : Exterior α) :
    reindex f (parityLinear u) = parityLinear (reindex f u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | single s r => simp

theorem reindex_extendDerivation (codeA : α → ℕ) (codeB : β → ℕ) (f : α ↪ β)
    (hf : ∀a b, codeB (f a) < codeB (f b) ↔ codeA a < codeA b)
    (D : α → Exterior α) (E : β → Exterior β)
    (hDE : ∀a, reindex f (D a) = E (f a)) (u : Exterior α) :
    reindex f (extendDerivation codeA D u) =
      extendDerivation codeB E (reindex f u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | single s r =>
    have hr : Finsupp.single s r = r • monomial s := by simp [monomial]
    rw [hr]
    simp only [map_smul]
    congr 1
    rw [reindex_monomial, extendDerivation_monomial, extendDerivation_monomial]
    simp only [map_sum, map_smul, Finset.sum_map, position_map codeA codeB f hf,
      reindex_wedge codeA codeB f hf, hDE, reindex_monomial, Finset.map_erase]

variable [GeneratorOrder α] [GeneratorOrder β]

def reindexAlgHom (f : α ↪ β)
    (hf : ∀a b, GeneratorOrder.code (f a) < GeneratorOrder.code (f b) ↔
      GeneratorOrder.code a < GeneratorOrder.code b) : Exterior α →ₐ[ℂ] Exterior β where
  toFun := reindex f
  map_zero' := map_zero (reindex f)
  map_add' := map_add (reindex f)
  map_one' := reindex_one f
  map_mul' := reindex_wedge _ _ f hf
  commutes' r := by
    change reindex f (Finsupp.single ∅ r) = Finsupp.single ∅ r
    simp

end KhanSL2.FiniteExterior
