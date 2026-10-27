module

public import KhanSL2.PVAMap

@[expose] public section

/-!
# Being an isomorphism is a property of a specified map

This predicate keeps the forward linear map fixed. It neither chooses an
unspecified map nor assumes its inverse in advance.
-/

noncomputable section

namespace KhanSL2

variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]

/-- A specified linear map is an isomorphism for all the graded differential
PVA operations. -/
structure IsGradedDifferentialPVAIsomorphism
    (DA : DifferentialData A) (brA : LambdaBracket A)
    (DB : DifferentialData B) (brB : LambdaBracket B)
    (f : A →ₗ[ℂ] B) : Prop where
  bijective : Function.Bijective f
  map_one : f DA.one = DB.one
  map_mul : ∀ a b, f (DA.mul a b) = DB.mul (f a) (f b)
  map_translation : ∀ a, f (DA.translation a) = DB.translation (f a)
  map_bracket : ∀ a b n, f (brA a b n) = brB (f a) (f b) n
  map_degree : ∀ d a, f a ∈ DB.piece d ↔ a ∈ DA.piece d

namespace IsGradedDifferentialPVAIsomorphism

variable {DA : DifferentialData A} {brA : LambdaBracket A}
  {DB : DifferentialData B} {brB : LambdaBracket B} {f : A →ₗ[ℂ] B}

/-- The inverse is constructed only after bijectivity of the specified map
has been proved. -/
def toEquiv (h : IsGradedDifferentialPVAIsomorphism DA brA DB brB f) :
    GradedDifferentialPVAEquiv DA brA DB brB where
  toLinearEquiv := LinearEquiv.ofBijective f h.bijective
  map_one := h.map_one
  map_mul := h.map_mul
  map_translation := h.map_translation
  map_bracket := h.map_bracket
  map_degree := h.map_degree

@[simp] theorem toEquiv_linearMap
    (h : IsGradedDifferentialPVAIsomorphism DA brA DB brB f) :
    h.toEquiv.toLinearEquiv.toLinearMap = f := rfl

theorem iff_exists_equiv :
    IsGradedDifferentialPVAIsomorphism DA brA DB brB f ↔
      ∃ e : GradedDifferentialPVAEquiv DA brA DB brB,
        e.toLinearEquiv.toLinearMap = f := by
  constructor
  · intro h
    exact ⟨h.toEquiv, rfl⟩
  · rintro ⟨e, rfl⟩
    exact ⟨e.toLinearEquiv.bijective, e.map_one, e.map_mul,
      e.map_translation, e.map_bracket, e.map_degree⟩

end IsGradedDifferentialPVAIsomorphism

set_option backward.isDefEq.respectTransparency false in
/-- An injective map preserving a genuine direct-sum grading also reflects
homogeneous degrees. -/
theorem graded_mem_iff_of_injective
    {PA : Degree → Submodule ℂ A} {PB : Degree → Submodule ℂ B}
    (hA : DirectSum.IsInternal PA) (hB : DirectSum.IsInternal PB)
    (f : A →ₗ[ℂ] B) (hf : Function.Injective f)
    (hg : ∀ d a, a ∈ PA d → f a ∈ PB d) (d : Degree) (a : A) :
    f a ∈ PB d ↔ a ∈ PA d := by
  classical
  let eA := LinearEquiv.ofBijective (DirectSum.coeLinearMap PA) hA
  let eB := LinearEquiv.ofBijective (DirectSum.coeLinearMap PB) hB
  have hcomp (t : DirectSum Degree fun e => PA e) :
      ((eB.symm (f (eA t))) d : B) = f (t d : A) := by
    induction t using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      by_cases hi : i = d
      · subst i
        simpa [eA, eB, LinearEquiv.ofBijective_apply] using congrArg (fun z : PB d => (z : B))
          (hB.ofBijective_coeLinearMap_of_mem (hg d x x.property))
      · simpa [eA, eB, LinearEquiv.ofBijective_apply,
          DirectSum.of_eq_of_ne _ _ _ (Ne.symm hi)] using
          congrArg (fun z : PB d => (z : B))
            (hB.ofBijective_coeLinearMap_of_mem_ne hi (hg i x x.property))
    | add u v hu hv => simpa using congrArg₂ (· + ·) hu hv
  constructor
  · intro ha
    have heq : f ((eA.symm a d : PA d) : A) = f a := by
      rw [← hcomp (eA.symm a), eA.apply_symm_apply]
      exact congrArg (fun z : PB d => (z : B))
        (hB.ofBijective_coeLinearMap_of_mem ha)
    rw [← hf heq]
    exact (eA.symm a d).property
  · exact hg d a

namespace PVAMap

variable {DA : DifferentialData A} {brA : LambdaBracket A}
  {DB : DifferentialData B} {brB : LambdaBracket B}

/-- Once a specified graded PVA morphism has been constructed, its
isomorphism assertion is exactly bijectivity. -/
theorem isomorphism_iff_bijective (f : PVAMap DA brA DB brB)
    (hA : DirectSum.IsInternal DA.piece) (hB : DirectSum.IsInternal DB.piece)
    (hg : ∀ d a, a ∈ DA.piece d → f.linear a ∈ DB.piece d) :
    IsGradedDifferentialPVAIsomorphism DA brA DB brB f.linear ↔
      Function.Bijective f.linear := by
  constructor
  · exact IsGradedDifferentialPVAIsomorphism.bijective
  · intro hf
    exact ⟨hf, f.map_one, f.map_mul, f.map_translation, f.map_bracket,
      graded_mem_iff_of_injective hA hB f.linear hf.injective hg⟩

end PVAMap
end KhanSL2
