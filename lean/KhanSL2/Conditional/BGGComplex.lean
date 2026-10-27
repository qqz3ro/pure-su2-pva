module

public import KhanSL2.Modules.BGGAssembly
public import KhanSL2.BGGBridge.TermVanishing
public import KhanSL2.Depth.Descent

@[expose] public section

/-!
# The actual coefficient BGG complex, assembled over spin

The terms below are algebraic sums of the already constructed BGG windows.
The differential is the restriction of the specified transferred differential
`BGGBridge.dHq`; no differential or comparison is supplied as an assumption.
-/

noncomputable section
open scoped DirectSum

namespace KhanSL2.Conditional.BGGComplex

open BGGBridge

/-- The actual BGG coefficient term, with finite spin support. -/
abbrev Term (B p : ℕ) := ⨁ S : ℤ, ↥(bggTerm p B S)

/-- The actual assembled BGG term vanishes above coefficient degree, without polynomial hypotheses. -/
theorem term_subsingleton_of_lt (B p : ℕ) (hp : B < p) : Subsingleton (Term B p) := by
  have : ∀ S : ℤ, Subsingleton ↥(bggTerm p B S) :=
    fun S => Submodule.subsingleton_iff_eq_bot.mpr (bggTerm_eq_bot_of_lt B p hp S)
  exact inferInstance

/-- The restriction of the actual BGG differential to one spin component. -/
def componentDifferential (B p : ℕ) (S : ℤ) :
    bggTerm (p + 1) B S →ₗ[ℂ] bggTerm p B S :=
  (dHq Current.NB).restrict (fun x hx => (bggWindow p B S).differential_mem x hx)

@[simp] theorem componentDifferential_coe (B p : ℕ) (S : ℤ)
    (x : bggTerm (p + 1) B S) :
    (componentDifferential B p S x : HarmN Current.NB ⧸ relH Current.NB) =
      dHq Current.NB x := rfl

/-- Assemble the actual differential without changing spin. -/
def differential (B p : ℕ) : Term B (p + 1) →ₗ[ℂ] Term B p :=
  DirectSum.lmap (componentDifferential B p)

@[simp] theorem differential_apply (B p : ℕ) (x : Term B (p + 1)) (S : ℤ) :
    differential B p x S = componentDifferential B p S (x S) := rfl

@[simp] theorem differential_lof (B p : ℕ) (S : ℤ) (x : bggTerm (p + 1) B S) :
    differential B p (DirectSum.lof ℂ ℤ (fun T => ↥(bggTerm (p + 1) B T)) S x) =
      DirectSum.lof ℂ ℤ (fun T => ↥(bggTerm p B T)) S
        (componentDifferential B p S x) :=
  DirectSum.lmap_lof (componentDifferential B p) S x

theorem componentDifferential_square_zero (B p : ℕ) (S : ℤ)
    (x : bggTerm (p + 1 + 1) B S) :
    componentDifferential B p S (componentDifferential B (p + 1) S x) = 0 := by
  apply Subtype.ext
  exact LinearMap.congr_fun dHq_comp_dHq x

theorem differential_comp_differential (B p : ℕ) :
    (differential B p).comp (differential B (p + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  apply DFinsupp.ext
  intro S
  exact componentDifferential_square_zero B p S (x S)

/-- The homology of this fixed, actual chain complex. -/
abbrev Homology (B p : ℕ) := Depth.homology (Term B) (differential B) p

/-- Degree-zero chains are cycles, in agreement with `Depth.homology`. -/
theorem dHq_zero_on_degree_zero (B : ℕ) (S : ℤ) (x : bggTerm 0 B S) :
    dHq Current.NB x = 0 := by
  obtain ⟨z, hz, hx⟩ := x.property
  rw [← hx]
  change Submodule.Quotient.mk (dH Current.NB z) = 0
  rw [dH_eq_zero_of_degH_zero hz.1.1, Submodule.Quotient.mk_zero]

end KhanSL2.Conditional.BGGComplex
