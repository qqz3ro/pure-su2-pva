module

public import KhanSL2.BGG.RootEnergy
public import KhanSL2.ExteriorRing
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Root supports are precisely the ordered-monomial basis of the concrete
exterior algebra on positive current root modes. -/

noncomputable section
open scoped BigOperators

namespace KhanSL2.BGG

abbrev RootMode := ℕ × Fin 3

instance : FiniteExterior.GeneratorOrder RootMode where
  code i := 3 * i.1 + i.2.val
  code_injective := by
    intro i j h
    dsimp at h
    apply Prod.ext
    · have hi := i.2.isLt
      have hj := j.2.isLt
      omega
    · apply Fin.ext
      have hi := i.2.isLt
      have hj := j.2.isLt
      omega

abbrev RootExterior := FiniteExterior.Exterior RootMode

def rootColorEmbedding (a : Fin 3) : ℕ ↪ RootMode where
  toFun n := (n, a)
  inj' := fun _ _ h => congrArg Prod.fst h

@[simp] theorem rootColorEmbedding_apply (a : Fin 3) (n : ℕ) :
    rootColorEmbedding a n = (n, a) := rfl

theorem rootColor_disjoint {a b : Fin 3} (hab : a ≠ b) (s t : Finset ℕ) :
    Disjoint (s.map (rootColorEmbedding a)) (t.map (rootColorEmbedding b)) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨n, _, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨m, _, hm⟩ := Finset.mem_map.mp hy
  exact hab (congrArg Prod.snd hm).symm

namespace RootSupport

def toFinset (w : RootSupport) : Finset RootMode :=
  w.pos.map (rootColorEmbedding 0) ∪ w.neutral.map (rootColorEmbedding 1) ∪
    w.neg.map (rootColorEmbedding 2)

@[simp] theorem mem_toFinset_zero (w : RootSupport) (n : ℕ) :
    (n, 0) ∈ w.toFinset ↔ n ∈ w.pos := by simp [toFinset]

@[simp] theorem mem_toFinset_one (w : RootSupport) (n : ℕ) :
    (n, 1) ∈ w.toFinset ↔ n ∈ w.neutral := by simp [toFinset]

@[simp] theorem mem_toFinset_two (w : RootSupport) (n : ℕ) :
    (n, 2) ∈ w.toFinset ↔ n ∈ w.neg := by simp [toFinset]

theorem sum_toFinset {A : Type*} [AddCommMonoid A] (w : RootSupport) (f : RootMode → A) :
    ∑ i ∈ w.toFinset, f i =
      (∑ n ∈ w.pos, f (n, 0)) + (∑ n ∈ w.neutral, f (n, 1)) +
        ∑ n ∈ w.neg, f (n, 2) := by
  have h01 := rootColor_disjoint (by decide : (0 : Fin 3) ≠ 1) w.pos w.neutral
  have h02 := rootColor_disjoint (by decide : (0 : Fin 3) ≠ 2) w.pos w.neg
  have h12 := rootColor_disjoint (by decide : (1 : Fin 3) ≠ 2) w.neutral w.neg
  rw [toFinset, Finset.sum_union (Finset.disjoint_union_left.mpr ⟨h02, h12⟩),
    Finset.sum_union h01]
  simp only [Finset.sum_map, rootColorEmbedding_apply]

theorem card_toFinset (w : RootSupport) : w.toFinset.card = w.degree := by
  simpa [degree] using sum_toFinset w (fun _ => (1 : ℕ))

end RootSupport

def colorFiber (s : Finset RootMode) (a : Fin 3) : Finset ℕ :=
  (s.filter fun i => i.2 = a).image Prod.fst

@[simp] theorem mem_colorFiber (s : Finset RootMode) (a : Fin 3) (n : ℕ) :
    n ∈ colorFiber s a ↔ (n, a) ∈ s := by
  simp only [colorFiber, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨m, b⟩, ⟨hm, hb⟩, hn⟩
    dsimp at hb hn
    subst m
    subst b
    exact hm
  · intro h
    exact ⟨(n, a), ⟨h, rfl⟩, rfl⟩

def supportOfFinset (s : Finset RootMode) : RootSupport :=
  ⟨colorFiber s 0, colorFiber s 1, colorFiber s 2⟩

@[simp] theorem supportOfFinset_toFinset (w : RootSupport) : supportOfFinset w.toFinset = w := by
  apply RootSupport.ext <;> ext n <;> simp [supportOfFinset]

@[simp] theorem toFinset_supportOfFinset (s : Finset RootMode) :
    (supportOfFinset s).toFinset = s := by
  ext i
  obtain ⟨n, a⟩ := i
  fin_cases a <;> simp [supportOfFinset]

def rootSupportEquiv : RootSupport ≃ Finset RootMode where
  toFun := RootSupport.toFinset
  invFun := supportOfFinset
  left_inv := supportOfFinset_toFinset
  right_inv := toFinset_supportOfFinset

/-- Exterior basis indexed by the three root supports. -/
def rootExteriorBasis : Module.Basis RootSupport ℂ RootExterior :=
  Finsupp.basisSingleOne.reindex rootSupportEquiv.symm

@[simp] theorem rootExteriorBasis_apply (w : RootSupport) :
    rootExteriorBasis w = FiniteExterior.monomial w.toFinset := by
  simp [rootExteriorBasis, rootSupportEquiv, FiniteExterior.monomial]

/-- Physical current energy of an exterior monomial. -/
def rootMonomialEnergy (s : Finset RootMode) : ℕ := ∑ i ∈ s, (i.1 + 1)

/-- Half the Cartan eigenvalue of each root generator. -/
def rootHalfWeight : Fin 3 → ℤ := ![1, 0, -1]

def rootMonomialWeight (s : Finset RootMode) : ℤ := ∑ i ∈ s, rootHalfWeight i.2

@[simp] theorem rootMonomialEnergy_toFinset (w : RootSupport) :
    rootMonomialEnergy w.toFinset = w.energy := by
  exact RootSupport.sum_toFinset w (fun i => i.1 + 1)

@[simp] theorem rootMonomialWeight_toFinset (w : RootSupport) :
    rootMonomialWeight w.toFinset = w.weight := by
  simpa [rootMonomialWeight, rootHalfWeight, RootSupport.weight, sub_eq_add_neg] using
    RootSupport.sum_toFinset w (fun i => rootHalfWeight i.2)

theorem triangular_le_rootMonomialEnergy (s : Finset RootMode) (j : ℕ)
    (hw : rootMonomialWeight s = j) : triangular j ≤ rootMonomialEnergy s := by
  have h := RootSupport.triangular_le_energy (supportOfFinset s) j
  rw [← rootMonomialWeight_toFinset, toFinset_supportOfFinset] at h
  simpa only [← rootMonomialEnergy_toFinset, toFinset_supportOfFinset] using h hw

theorem rootMonomial_eq_highest_of_minimal_energy (s : Finset RootMode) (j : ℕ)
    (hw : rootMonomialWeight s = j) (he : rootMonomialEnergy s = triangular j) :
    s = (RootSupport.highest j).toFinset := by
  have h := RootSupport.eq_highest_of_minimal_energy (supportOfFinset s) j
  rw [← rootMonomialWeight_toFinset, toFinset_supportOfFinset,
    ← rootMonomialEnergy_toFinset, toFinset_supportOfFinset] at h
  simpa using congrArg RootSupport.toFinset (h hw he)

end KhanSL2.BGG