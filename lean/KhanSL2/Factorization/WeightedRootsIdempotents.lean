module

public import KhanSL2.Factorization.WeightedRootsBasic
public import Mathlib.RingTheory.Idempotents
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Boolean root assignments give a complete orthogonal system of idempotents.
This decomposition is valid before any reduction of the coefficient ring. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.Factorization.WeightedRoots

variable {A : Type*} [CommRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Select an idempotent or its complement according to a root assignment. -/
def choice (e : ι → A) (σ : ι → Bool) (i : ι) : A :=
  if σ i then e i else 1 - e i

/-- The component where exactly the specified roots belong to the first factor. -/
def assignment (e : ι → A) (σ : ι → Bool) : A := ∏ i, choice e σ i

omit [Fintype ι] [DecidableEq ι] in
theorem choice_isIdempotent (e : ι → A) (he : ∀ i, IsIdempotentElem (e i))
    (σ : ι → Bool) (i : ι) : IsIdempotentElem (choice e σ i) := by
  unfold choice
  split
  · exact he i
  · exact (he i).one_sub

omit [DecidableEq ι] in
theorem assignment_isIdempotent (e : ι → A) (he : ∀ i, IsIdempotentElem (e i))
    (σ : ι → Bool) : IsIdempotentElem (assignment e σ) := by
  change (∏ i, choice e σ i) * (∏ i, choice e σ i) = ∏ i, choice e σ i
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun i _ => (choice_isIdempotent e he σ i).eq)

omit [DecidableEq ι] in
theorem choice_dvd_assignment (e : ι → A) (σ : ι → Bool) (i : ι) :
    choice e σ i ∣ assignment e σ :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

omit [DecidableEq ι] in
theorem assignment_mul_selector (e : ι → A) (he : ∀ i, IsIdempotentElem (e i))
    (σ : ι → Bool) (i : ι) :
    assignment e σ * e i = if σ i then assignment e σ else 0 := by
  obtain ⟨q,hq⟩ := choice_dvd_assignment e σ i
  cases hσ : σ i
  · simp only [hσ,Bool.false_eq_true,if_false]
    rw [hq]
    simp only [choice,hσ,Bool.false_eq_true,if_false]
    calc
      (1-e i)*q*e i = q*(e i-e i*e i) := by ring
      _ = 0 := by rw [(he i).eq,sub_self,mul_zero]
  · simp only [hσ,if_true]
    rw [hq]
    simp only [choice,hσ,if_true]
    calc
      e i*q*e i = (e i*e i)*q := by ring
      _ = e i*q := by rw [(he i).eq]

omit [DecidableEq ι] in
theorem assignment_orthogonal (e : ι → A) (he : ∀ i, IsIdempotentElem (e i)) :
    Pairwise (fun σ τ : ι → Bool => assignment e σ * assignment e τ = 0) := by
  classical
  intro σ τ hστ
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hστ
  have hz : choice e σ i * choice e τ i = 0 := by
    cases hs : σ i <;> cases ht : τ i <;>
      simp_all only [choice,Bool.false_eq_true,if_false,if_true,mul_sub,sub_mul,mul_one,
        one_mul,(he i).eq,sub_self,ne_eq,not_true_eq_false]
  obtain ⟨q,hq⟩ := choice_dvd_assignment e σ i
  obtain ⟨r,hr⟩ := choice_dvd_assignment e τ i
  rw [hq,hr]
  calc
    choice e σ i*q*(choice e τ i*r) = (choice e σ i*choice e τ i)*(q*r) := by ring
    _ = 0 := by rw [hz,zero_mul]

theorem assignment_sum (e : ι → A) : ∑ σ : ι → Bool, assignment e σ = 1 := by
  classical
  unfold assignment choice
  rw [← Fintype.prod_sum (fun (i : ι) (b : Bool) => if b then e i else 1-e i)]
  simp

theorem assignment_complete (e : ι → A) (he : ∀ i, IsIdempotentElem (e i)) :
    CompleteOrthogonalIdempotents (assignment e) where
  idem := assignment_isIdempotent e he
  ortho := assignment_orthogonal e he
  complete := assignment_sum e

/-- The actual quotient ring of one Boolean root-assignment component. -/
def componentIdeal (e : ι → A) (σ : ι → Bool) : Ideal A :=
  Ideal.span {1 - assignment e σ}

abbrev Component (e : ι → A) (σ : ι → Bool) := A ⧸ componentIdeal e σ

/-- Chinese remainder splitting for all root assignments. -/
def assignmentEquiv (e : ι → A) (he : ∀ i, IsIdempotentElem (e i)) :
    A ≃+* ∀ σ : ι → Bool, Component e σ :=
  RingEquiv.ofBijective (RingHom.pi fun σ => Ideal.Quotient.mk (componentIdeal e σ))
    (assignment_complete e he).bijective_pi

@[simp] theorem assignmentEquiv_apply (e : ι → A) (he : ∀ i, IsIdempotentElem (e i))
    (a : A) (σ : ι → Bool) : assignmentEquiv e he a σ = Ideal.Quotient.mk _ a := rfl

omit [DecidableEq ι] in
theorem assignment_eq_one_in_component (e : ι → A) (σ : ι → Bool) :
    Ideal.Quotient.mk (componentIdeal e σ) (assignment e σ) = 1 := by
  have h : Ideal.Quotient.mk (componentIdeal e σ) (1-assignment e σ) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [map_sub,map_one] at h
  exact (sub_eq_zero.mp h).symm

omit [DecidableEq ι] in
theorem selector_in_component (e : ι → A) (he : ∀ i, IsIdempotentElem (e i))
    (σ : ι → Bool) (i : ι) :
    Ideal.Quotient.mk (componentIdeal e σ) (e i) = if σ i then 1 else 0 := by
  have h := congrArg (Ideal.Quotient.mk (componentIdeal e σ)) (assignment_mul_selector e he σ i)
  rw [map_mul,assignment_eq_one_in_component,one_mul] at h
  cases hs : σ i <;> simpa only [hs,if_true,Bool.false_eq_true,if_false,map_zero,
    assignment_eq_one_in_component] using h

end KhanSL2.Factorization.WeightedRoots



