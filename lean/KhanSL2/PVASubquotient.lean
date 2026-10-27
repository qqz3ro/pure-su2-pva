module

public import KhanSL2.PVATransport
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.BilinearMap

@[expose] public section

/-! Actual restricted and quotient PVA operations, with their defining maps. -/

noncomputable section

namespace KhanSL2

variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]

def restrictPolynomial (S : Submodule ℂ A) (p : LambdaPolynomial A)
    (hp : ∀ n, p n ∈ S) : LambdaPolynomial S :=
  Finsupp.onFinset p.support (fun n => ⟨p n, hp n⟩)
    (fun _ hn => Finsupp.mem_support_iff.mpr fun hz => hn (Subtype.ext hz))

@[simp] theorem restrictPolynomial_apply (S : Submodule ℂ A)
    (p : LambdaPolynomial A) (hp : ∀ n, p n ∈ S) (n : ℕ) :
    (restrictPolynomial S p hp n : A) = p n := rfl

structure PVAClosedSubmodule (D : DifferentialData A) (br : LambdaBracket A)
    (S : Submodule ℂ A) : Prop where
  one_mem : D.one ∈ S
  mul_mem : ∀ a b, a ∈ S → b ∈ S → D.mul a b ∈ S
  translation_mem : ∀ a, a ∈ S → D.translation a ∈ S
  bracket_mem : ∀ a b n, a ∈ S → b ∈ S → br a b n ∈ S

namespace PVAClosedSubmodule

variable {D : DifferentialData A} {br : LambdaBracket A}
  {S : Submodule ℂ A} (h : PVAClosedSubmodule D br S)

def mul : S →ₗ[ℂ] S →ₗ[ℂ] S where
  toFun a := LinearMap.codRestrict S ((D.mul a).comp S.subtype)
    (fun b => h.mul_mem a b a.property b.property)
  map_add' a b := by ext c; exact D.mul.map_add₂ a b c
  map_smul' r a := by ext b; exact D.mul.map_smul₂ r a b

def translation : Module.End ℂ S :=
  LinearMap.codRestrict S (D.translation.comp S.subtype)
    (fun a => h.translation_mem a a.property)

def data : DifferentialData S where
  one := ⟨D.one, h.one_mem⟩
  mul := h.mul
  translation := h.translation
  piece d := (D.piece d).comap S.subtype

def bracket : LambdaBracket S where
  toFun a :=
    { toFun := fun b => restrictPolynomial S (br a b)
        (fun n => h.bracket_mem a b n a.property b.property)
      map_add' := by
        intro b c
        apply Finsupp.ext
        intro n
        apply Subtype.ext
        exact congrArg (fun p : LambdaPolynomial A => p n) ((br a).map_add b c)
      map_smul' := by
        intro r b
        apply Finsupp.ext
        intro n
        apply Subtype.ext
        exact congrArg (fun p : LambdaPolynomial A => p n) ((br a).map_smul r b) }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    apply Finsupp.ext
    intro n
    apply Subtype.ext
    exact congrArg (fun p : LambdaPolynomial A => p n) (br.map_add₂ a b c)
  map_smul' r a := by
    apply LinearMap.ext
    intro b
    apply Finsupp.ext
    intro n
    apply Subtype.ext
    exact congrArg (fun p : LambdaPolynomial A => p n) (br.map_smul₂ r a b)

def inclusion : PVAMap h.data h.bracket D br where
  linear := S.subtype
  map_one := rfl
  map_mul _ _ := rfl
  map_translation _ := rfl
  map_bracket _ _ _ := rfl

theorem isPVA (hi : DirectSum.IsInternal h.data.piece) (hD : IsPVA D br) :
    IsPVA h.data h.bracket :=
  h.inclusion.pva_of_injective Subtype.val_injective (fun _ _ => Iff.rfl) hi hD

end PVAClosedSubmodule

def quotientBilinear (S : Submodule ℂ A) (F : A →ₗ[ℂ] A →ₗ[ℂ] B)
    (hleft : ∀ a ∈ S, ∀ b, F a b = 0)
    (hright : ∀ a b, b ∈ S → F a b = 0) :
    (A ⧸ S) →ₗ[ℂ] (A ⧸ S) →ₗ[ℂ] B :=
  S.liftQ
    { toFun := fun a => S.liftQ (F a) (fun b hb => hright a b hb)
      map_add' := by
        intro a b
        apply LinearMap.ext
        intro c
        induction c using Quotient.inductionOn' with
        | _ c => exact F.map_add₂ a b c
      map_smul' := by
        intro r a
        apply LinearMap.ext
        intro b
        induction b using Quotient.inductionOn' with
        | _ b => exact F.map_smul₂ r a b }
    (by
      intro a ha
      apply LinearMap.ext
      intro b
      induction b using Quotient.inductionOn' with
      | _ b => exact hleft a ha b)

@[simp] theorem quotientBilinear_mk (S : Submodule ℂ A) (F : A →ₗ[ℂ] A →ₗ[ℂ] B)
    (hleft : ∀ a ∈ S, ∀ b, F a b = 0)
    (hright : ∀ a b, b ∈ S → F a b = 0) (a b : A) :
    quotientBilinear S F hleft hright (S.mkQ a) (S.mkQ b) = F a b := rfl

structure PVAIdeal (D : DifferentialData A) (br : LambdaBracket A)
    (S : Submodule ℂ A) : Prop where
  mul_left : ∀ a b, a ∈ S → D.mul a b ∈ S
  mul_right : ∀ a b, b ∈ S → D.mul a b ∈ S
  translation_mem : ∀ a, a ∈ S → D.translation a ∈ S
  bracket_left : ∀ a b n, a ∈ S → br a b n ∈ S
  bracket_right : ∀ a b n, b ∈ S → br a b n ∈ S

namespace PVAIdeal

variable {D : DifferentialData A} {br : LambdaBracket A}
  {S : Submodule ℂ A} (h : PVAIdeal D br S)

def mul : (A ⧸ S) →ₗ[ℂ] (A ⧸ S) →ₗ[ℂ] (A ⧸ S) :=
  quotientBilinear S (D.mul.compr₂ S.mkQ)
    (fun a ha b => (Submodule.Quotient.mk_eq_zero S).mpr (h.mul_left a b ha))
    (fun a b hb => (Submodule.Quotient.mk_eq_zero S).mpr (h.mul_right a b hb))

def translation : Module.End ℂ (A ⧸ S) :=
  S.mapQ S D.translation (fun a ha => h.translation_mem a ha)

def data : DifferentialData (A ⧸ S) where
  one := S.mkQ D.one
  mul := h.mul
  translation := h.translation
  piece d := (D.piece d).map S.mkQ

def bracket : LambdaBracket (A ⧸ S) :=
  quotientBilinear S (br.compr₂ (coefficientMap S.mkQ))
    (by
      intro a ha b
      apply Finsupp.ext
      intro n
      exact (Submodule.Quotient.mk_eq_zero S).mpr (h.bracket_left a b n ha))
    (by
      intro a b hb
      apply Finsupp.ext
      intro n
      exact (Submodule.Quotient.mk_eq_zero S).mpr (h.bracket_right a b n hb))

def projection : PVAMap D br h.data h.bracket where
  linear := S.mkQ
  map_one := rfl
  map_mul _ _ := rfl
  map_translation _ := rfl
  map_bracket _ _ _ := rfl

theorem isPVA (hi : DirectSum.IsInternal h.data.piece) (hD : IsPVA D br) :
    IsPVA h.data h.bracket :=
  h.projection.pva_of_surjective S.mkQ_surjective (fun _ => rfl) hi hD

end PVAIdeal
end KhanSL2
