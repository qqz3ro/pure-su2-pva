module

public import KhanSL2.BGGBridge.TrivialCoefficients

@[expose] public section

/-!
# Milestone: the BGG complex computes `K p B S`

Notation: `𝔤 = 𝔰𝔩₂`, `𝔩 = 𝔤[z]`, `𝔩₊ = z𝔤[z]`, `N = Λ(ε𝔩)` (`NB`), and
`K p B S = H_p(𝔩, 𝔤; Λ^B(ε𝔩))_S` is milestone M2's relative homology.

**The BGG complex.** `Harm = ker □ ⊆ Λ𝔩₊` is the harmonic part of the positive CE complex,
with `Harm = ⨁ₚ Harmₚ` and `Harmₚ ≅ V(2p)` as `𝔤`-modules (`harmonicDegree_standard`). The
BGG development's special contraction of the free CE resolution of `𝔩₊` onto
`U(𝔩₊) ⊗ Harm` is base-changed along `N` (`BGGBridge.cN`) and passed to `𝔤`-coinvariants
(`BGGBridge.qcN`). The result is a complex

  `BGGComplex = (Harm ⊗ N)_𝔤`, with differential `dHq NB` (`bggDifferential_sq`).

Its piece `bggTerm p B S` is the image of the part of `Harmₚ ⊗ Λ^B(ε𝔩)` of spin `S`.

**The bridge.** The base-changed chains `Λ𝔩₊ ⊗ N` are M2's chains, by an isomorphism `J` that
matches the boundaries, the `𝔤`-relations and the three gradings. So the contraction lives
on M2's relative complex. The homotopy raises `p` by one, which gives

  `kEquivBGGHomology p B S : K p B S ≃ₗ[ℂ] BGGHomology p B S`.

**Trivial coefficients.** For `B = 0` the BGG terms are `V(2p)_𝔤`, which is `ℂ` for `p = 0`
and `0` otherwise. Hence `K p 0 S` is `ℂ` for `p = S = 0` and `0` otherwise, and through the
dictionary the restricted relative cohomology in degree `(p, 0, S)` is `ℂ · [1]` at
`(0, 0, 0)` and zero elsewhere (`cohomology_B_zero`). This is the blueprint's corollary
`cor:trivialcurrent`, proved here outright instead of from `BGGInput`.

**Not covered.** The blueprint's consumer form `BGGInput` also asks for `R_B`-linearity
(which needs the model of WP8) and for an identification of the terms with
`(N_B ⊗ V(2p))^𝔤`. Here the terms are the graded pieces of the coinvariants, inside the
image of `Harmₚ ⊗ Λ^B(ε𝔩)`.
-/

noncomputable section

namespace KhanSL2.Current

open KhanSL2.BGG KhanSL2.BGGBridge

/-- The BGG complex: harmonic chains `Harm ⊗ Λ(ε𝔩)` modulo the `𝔤`-relations. -/
abbrev BGGComplex : Type := HarmN NB ⧸ relH NB

/-- The BGG differential squares to zero. -/
theorem bggDifferential_sq : (dHq NB).comp (dHq NB) = 0 := dHq_comp_dHq

/-- The BGG term in degree `p` comes from harmonic degree `p`. -/
theorem bggTerm_le_harmonicDegree (p B : ℕ) (S : ℤ) :
    bggTerm p B S ≤ (tensorLeft (N := NB) (degH p)).map (relH NB).mkQ :=
  Submodule.map_mono (inf_le_left.trans inf_le_left)

/-- Harmonic degree `p` is the standard representation `V(2p)`. -/
theorem harmonicDegree_standard (p : ℕ) :
    Nonempty (PositiveCE.harmonicDegree p ≃ₗ⁅ℂ,G⁆ TauCeti.Sl2Std ℂ (2 * p)) :=
  ⟨PositiveCE.harmonicDegreeStandardEquiv p⟩

/-- **`K p B S` is the homology of the BGG complex** in degree `p`, coefficient degree `B` and
spin `S`. -/
def kEquivBGGHomology (p B : ℕ) (S : ℤ) : K p B S ≃ₗ[ℂ] BGGHomology p B S :=
  kEquivBGG p B S

/-- **`H_p(𝔩, 𝔤; ℂ)_S`.** -/
theorem finrank_K_B_zero (p : ℕ) (S : ℤ) :
    Module.finrank ℂ (K p 0 S) = if p = 0 ∧ S = 0 then 1 else 0 :=
  finrank_K_trivial p S

/-- **The milestone in one statement.** -/
theorem milestoneBGGBridge :
    (∀ (p B : ℕ) (S : ℤ), Nonempty (K p B S ≃ₗ[ℂ] BGGHomology p B S)) ∧
      (dHq NB).comp (dHq NB) = 0 ∧
      (∀ p : ℕ, Nonempty (PositiveCE.harmonicDegree p ≃ₗ⁅ℂ,G⁆ TauCeti.Sl2Std ℂ (2 * p))) ∧
      (∀ (p : ℕ) (S : ℤ), Module.finrank ℂ (K p 0 S) = if p = 0 ∧ S = 0 then 1 else 0) ∧
      (∀ (p : ℕ) (S : ℤ), ¬(p = 0 ∧ S = 0) → cohomologyPiece (kDegree p 0 S) = ⊥) ∧
      cohomologyPiece (kDegree 0 0 0) = ℂ ∙ classOf cochainOne one_mem_cycles :=
  ⟨fun p B S => ⟨kEquivBGG p B S⟩, dHq_comp_dHq, harmonicDegree_standard, finrank_K_trivial,
    cohomology_B_zero.1, cohomology_B_zero.2⟩

end KhanSL2.Current
