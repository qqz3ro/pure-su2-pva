module

public import KhanSL2.Factorization.NonnegativeConeMaps

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace KhanSL2.Factorization.NonnegativeCone

universe u v
variable {R : Type u} [CommRing R]
variable {C₁ C₂ C₃ D₁ D₂ D₃ : ChainComplex (ModuleCat.{v} R) ℕ}
variable (iC : C₁ ⟶ C₂) (pC : C₂ ⟶ C₃) (iD : D₁ ⟶ D₂) (pD : D₂ ⟶ D₃)
variable (φ₁ : C₁ ⟶ D₁) (φ₂ : C₂ ⟶ D₂) (φ₃ : C₃ ⟶ D₃)
variable (hi : φ₁ ≫ iD = iC ≫ φ₂) (hp : φ₂ ≫ pD = pC ≫ φ₃)
variable (hinjC : ∀ n, Function.Injective (iC.f n))
    (hexC : ∀ n, Function.Exact (iC.f n) (pC.f n))
    (hsurjC : ∀ n, Function.Surjective (pC.f n))
    (hinjD : ∀ n, Function.Injective (iD.f n))
    (hexD : ∀ n, Function.Exact (iD.f n) (pD.f n))
    (hsurjD : ∀ n, Function.Surjective (pD.f n))

include hinjC hexC hsurjC hinjD hexD hsurjD in
/-- A morphism of degreewise short exact rows induces a degreewise short exact
sequence of the genuine nonnegative comparison cones. -/
theorem mapComplex_shortExact (n : ℕ) :
    Function.Injective ((mapComplex φ₁ φ₂ iC iD hi).f n) ∧
      Function.Exact ((mapComplex φ₁ φ₂ iC iD hi).f n)
        ((mapComplex φ₂ φ₃ pC pD hp).f n) ∧
      Function.Surjective ((mapComplex φ₂ φ₃ pC pD hp).f n) := by
  cases n with
  | zero => exact ⟨hinjD 0,hexD 0,hsurjD 0⟩
  | succ n =>
    constructor
    · rintro ⟨y,x⟩ ⟨y',x'⟩ h
      exact Prod.ext (hinjD (n+1) (congrArg Prod.fst h)) (hinjC n (congrArg Prod.snd h))
    constructor
    · intro z
      rcases z with ⟨y,x⟩
      change (pD.f (n+1) y,pC.f n x) = (0,0) ↔
        ∃ z : D₁.X (n+1) × C₁.X n, (iD.f (n+1) z.1,iC.f n z.2) = (y,x)
      constructor
      · intro h
        obtain ⟨y₀,hy⟩ := (hexD (n+1) y).mp (congrArg Prod.fst h)
        obtain ⟨x₀,hx⟩ := (hexC n x).mp (congrArg Prod.snd h)
        exact ⟨(y₀,x₀),Prod.ext hy hx⟩
      · rintro ⟨⟨y₀,x₀⟩,h⟩
        exact Prod.ext ((hexD (n+1) y).mpr ⟨y₀,congrArg Prod.fst h⟩)
          ((hexC n x).mpr ⟨x₀,congrArg Prod.snd h⟩)
    · rintro ⟨y,x⟩
      obtain ⟨y₀,hy⟩ := hsurjD (n+1) y
      obtain ⟨x₀,hx⟩ := hsurjC n x
      exact ⟨(y₀,x₀),Prod.ext hy hx⟩

include iC pC iD pD hi hp hinjC hexC hsurjC hinjD hexD hsurjD in
/-- Extension closure for a natural comparison, with only termwise exact rows. -/
theorem quasiIso_of_shortExact_rows [QuasiIso φ₁] [QuasiIso φ₃] : QuasiIso φ₂ := by
  have h := mapComplex_shortExact iC pC iD pD φ₁ φ₂ φ₃ hi hp hinjC hexC hsurjC hinjD hexD hsurjD
  exact quasiIso_of_acyclic φ₂ (ComplexExactness.acyclic_of_shortExact
    (mapComplex φ₁ φ₂ iC iD hi) (mapComplex φ₂ φ₃ pC pD hp)
    (fun n => (h n).1) (fun n => (h n).2.1) (fun n => (h n).2.2)
    (acyclic_of_quasiIso φ₁) (acyclic_of_quasiIso φ₃))

include iC pC iD pD hi hp hinjC hexC hsurjC hinjD hexD hsurjD in
/-- Quotient step used to extract a top constituent from a symmetric model. -/
theorem quasiIso_quotient_of_shortExact_rows [QuasiIso φ₁] [QuasiIso φ₂] : QuasiIso φ₃ := by
  have h := mapComplex_shortExact iC pC iD pD φ₁ φ₂ φ₃ hi hp hinjC hexC hsurjC hinjD hexD hsurjD
  exact quasiIso_of_acyclic φ₃ (ComplexExactness.acyclic_quotient_of_shortExact
    (mapComplex φ₁ φ₂ iC iD hi) (mapComplex φ₂ φ₃ pC pD hp)
    (fun n => (h n).1) (fun n => (h n).2.1) (fun n => (h n).2.2)
    (acyclic_of_quasiIso φ₁) (acyclic_of_quasiIso φ₂))

include iC pC iD pD hi hp hinjC hexC hsurjC hinjD hexD hsurjD in
/-- Submodule step, completing all three short-exact two-out-of-three directions. -/
theorem quasiIso_subcomplex_of_shortExact_rows [QuasiIso φ₂] [QuasiIso φ₃] : QuasiIso φ₁ := by
  have h := mapComplex_shortExact iC pC iD pD φ₁ φ₂ φ₃ hi hp hinjC hexC hsurjC hinjD hexD hsurjD
  exact quasiIso_of_acyclic φ₁ (ComplexExactness.acyclic_subcomplex_of_shortExact
    (mapComplex φ₁ φ₂ iC iD hi) (mapComplex φ₂ φ₃ pC pD hp)
    (fun n => (h n).1) (fun n => (h n).2.1) (fun n => (h n).2.2)
    (acyclic_of_quasiIso φ₂) (acyclic_of_quasiIso φ₃))

/-- A natural comparison retract preserves quasi-isomorphisms. This is the
precise direct-summand step; both retractions here are actual chain maps. -/
theorem quasiIso_of_retract_square
    (iC : C₁ ⟶ C₂) (rC : C₂ ⟶ C₁) (iD : D₁ ⟶ D₂) (rD : D₂ ⟶ D₁)
    (φ₁ : C₁ ⟶ D₁) (φ₂ : C₂ ⟶ D₂)
    (hi : φ₁ ≫ iD = iC ≫ φ₂) (hr : φ₂ ≫ rD = rC ≫ φ₁)
    (hC : iC ≫ rC = 𝟙 C₁) (hD : iD ≫ rD = 𝟙 D₁)
    [QuasiIso φ₂] : QuasiIso φ₁ := by
  let h : RetractArrow φ₁ φ₂ :=
    { i := Arrow.homMk iC iD hi.symm
      r := Arrow.homMk rC rD hr.symm
      retract := Arrow.hom_ext _ _ hC hD }
  exact quasiIso_of_retractArrow h

end KhanSL2.Factorization.NonnegativeCone