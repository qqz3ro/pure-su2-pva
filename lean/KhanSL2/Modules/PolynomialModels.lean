module

public import KhanSL2.Injectivity.BlockSymmetry
public import KhanSL2.Injectivity.VandermondeFactors

@[expose] public section

/-!
# The concrete symmetric rings and source polynomial modules

`R B` is the symmetric subalgebra of the polynomial ring on `B` labelled roots.
`S r s` consists of polynomials symmetric separately in the two alphabets.
`J r s` is the actual polynomial image `discriminantFactor r s * S r s`.
No identification with a source dual is used in these definitions.
-/

noncomputable section

namespace KhanSL2.Modules

open MvPolynomial
open Injectivity

/-- The coefficient ring on `B` unordered roots. -/
abbrev R (B : ℕ) := ↥(MvPolynomial.symmetricSubalgebra (Fin B) ℂ)

/-- Polynomials in the two labelled alphabets. -/
abbrev Polynomial (r s : ℕ) := MvPolynomial (Fin r ⊕ Fin s) ℂ

/-- Symmetry in each alphabet separately. -/
def IsBlockSymmetric {r s : ℕ} (q : Polynomial r s) : Prop :=
  ∀ (e : Equiv.Perm (Fin r)) (f : Equiv.Perm (Fin s)),
    rename (Equiv.sumCongr e f) q = q

/-- The subalgebra fixed by the permutations of the two alphabets. -/
def blockSymmetric (r s : ℕ) : Subalgebra ℂ (Polynomial r s) where
  carrier := {q | IsBlockSymmetric q}
  algebraMap_mem' c e f := rename_C _ c
  mul_mem' hp hq e f := by rw [map_mul, hp e f, hq e f]
  add_mem' hp hq e f := by rw [map_add, hp e f, hq e f]

/-- The ring of separately symmetric polynomials. -/
abbrev S (r s : ℕ) := ↥(blockSymmetric r s)

@[simp] theorem mem_blockSymmetric {r s : ℕ} (q : Polynomial r s) :
    q ∈ blockSymmetric r s ↔ IsBlockSymmetric q := Iff.rfl

/-- Multiples of the explicit discriminant factor by separately symmetric polynomials. -/
def JSubmodule (r s : ℕ) : Submodule (S r s) (Polynomial r s) where
  carrier := {q | ∃ a : S r s, q = discriminantFactor r s * (a : Polynomial r s)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro q t ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by simp [mul_add]⟩
  smul_mem' := by
    rintro a q ⟨b, rfl⟩
    refine ⟨a * b, ?_⟩
    change (a : Polynomial r s) * (discriminantFactor r s * (b : Polynomial r s)) =
      discriminantFactor r s * ((a : Polynomial r s) * (b : Polynomial r s))
    ring

/-- The actual polynomial module `F_{r,s} S_{r,s}`. -/
abbrev J (r s : ℕ) := ↥(JSubmodule r s)

@[simp] theorem mem_JSubmodule_iff {r s : ℕ} (q : Polynomial r s) :
    q ∈ JSubmodule r s ↔
      ∃ a : Polynomial r s, IsBlockSymmetric a ∧ q = discriminantFactor r s * a := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, a.property, ha⟩
  · rintro ⟨a, ha, hq⟩
    exact ⟨⟨a, ha⟩, hq⟩

/-- A criterion for landing in `J`: divisibility and the source permutation character. -/
theorem mem_JSubmodule_iff_dvd_character {r s : ℕ} (q : Polynomial r s) :
    q ∈ JSubmodule r s ↔ discriminantFactor r s ∣ q ∧
      ∀ (e : Equiv.Perm (Fin r)) (f : Equiv.Perm (Fin s)),
        rename (Equiv.sumCongr e f) q = (f.sign : Polynomial r s) * q := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨dvd_mul_right _ _, fun e f => ?_⟩
    rw [map_mul, rename_discriminantFactor, a.property e f]
    ring
  · rintro ⟨⟨a, ha⟩, hq⟩
    exact ⟨⟨a, discriminant_quotient_symmetric ha hq⟩, ha⟩

/-- The defining multiplication map, with the image retained as a polynomial subtype. -/
def discriminantMul (r s : ℕ) : S r s →ₗ[S r s] J r s where
  toFun a := ⟨discriminantFactor r s * (a : Polynomial r s), ⟨a, rfl⟩⟩
  map_add' a b := by apply Subtype.ext; simp [mul_add]
  map_smul' a b := by
    apply Subtype.ext
    change discriminantFactor r s * ((a : Polynomial r s) * (b : Polynomial r s)) =
      (a : Polynomial r s) * (discriminantFactor r s * (b : Polynomial r s))
    ring

@[simp] theorem discriminantMul_coe (r s : ℕ) (a : S r s) :
    (discriminantMul r s a : Polynomial r s) = discriminantFactor r s * (a : Polynomial r s) :=
  rfl

theorem discriminantMul_injective (r s : ℕ) : Function.Injective (discriminantMul r s) := by
  intro a b h
  apply Subtype.ext
  have h' := congrArg (fun q : J r s => (q : Polynomial r s)) h
  exact mul_left_cancel₀ (discriminantFactor_ne_zero r s) h'

theorem discriminantMul_surjective (r s : ℕ) : Function.Surjective (discriminantMul r s) := by
  rintro ⟨q, a, ha⟩
  exact ⟨a, Subtype.ext ha.symm⟩

/-- `J` is a free rank-one module over its own block-symmetric ring. -/
def discriminantMulEquiv (r s : ℕ) : S r s ≃ₗ[S r s] J r s :=
  LinearEquiv.ofBijective (discriminantMul r s)
    ⟨discriminantMul_injective r s, discriminantMul_surjective r s⟩

end KhanSL2.Modules
