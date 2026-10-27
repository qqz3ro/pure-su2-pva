module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

/-!
# Symmetric functions in two blocks of variables

`S_{r,s} = ℂ[z₁, …, z_r]^{S_r} ⊗ ℂ[w₁, …, w_s]^{S_s}` is the subalgebra of `ℂ[z, w]` of
polynomials symmetric in `z` and in `w` separately (`symmBoth`). The fundamental theorem of
symmetric polynomials, in each block, says that
`blockE : ℂ[α₁, …, α_r, β₁, …, β_s] → ℂ[z, w]`, `α_j ↦ e_j(z)`, `β_j ↦ e_j(w)`,
is injective with image `S_{r,s}` (`blockE_injective`, `mem_symmBoth_iff`).

The proof writes `ℂ[z, w] = ℂ[w][z]`: a polynomial symmetric in `z` is a polynomial in the
`e_j(z)` with coefficients in `ℂ[w]`, uniquely; symmetry in `w` then passes to these
coefficients.
-/

noncomputable section

open MvPolynomial

namespace KhanSL2.Depth

variable (r s : ℕ)

/-- `ℂ[z₁, …, z_r, w₁, …, w_s]`: `X (inl i)` is `z_{i+1}`, `X (inr a)` is `w_{a+1}`. -/
abbrev ZW (r s : ℕ) : Type := MvPolynomial (Fin r ⊕ Fin s) ℂ

/-- **`S_{r,s}`**: polynomials symmetric in `z` and in `w` separately. -/
def symmBoth : Subalgebra ℂ (ZW r s) where
  carrier := {f | ∀ (σ : Equiv.Perm (Fin r)) (τ : Equiv.Perm (Fin s)),
    rename (Sum.map σ τ) f = f}
  mul_mem' {a b} ha hb σ τ := by rw [map_mul, ha σ τ, hb σ τ]
  add_mem' {a b} ha hb σ τ := by rw [map_add, ha σ τ, hb σ τ]
  algebraMap_mem' c σ τ := by rw [MvPolynomial.algebraMap_eq, rename_C]

theorem mem_symmBoth {f : ZW r s} :
    f ∈ symmBoth r s ↔ ∀ (σ : Equiv.Perm (Fin r)) (τ : Equiv.Perm (Fin s)),
      rename (Sum.map σ τ) f = f := Iff.rfl

/-- The elementary symmetric functions of the two blocks. -/
def blockEsymm : Fin r ⊕ Fin s → ZW r s
  | Sum.inl j => rename Sum.inl (esymm (Fin r) ℂ ((j : ℕ) + 1))
  | Sum.inr j => rename Sum.inr (esymm (Fin s) ℂ ((j : ℕ) + 1))

/-- `α_j ↦ e_{j+1}(z)`, `β_j ↦ e_{j+1}(w)`. -/
def blockE : MvPolynomial (Fin r ⊕ Fin s) ℂ →ₐ[ℂ] ZW r s := aeval (blockEsymm r s)

theorem blockEsymm_mem (v : Fin r ⊕ Fin s) : blockEsymm r s v ∈ symmBoth r s := by
  intro σ τ
  rcases v with j | j
  · rw [blockEsymm, rename_rename]
    have : (Sum.map σ τ ∘ Sum.inl : Fin r → Fin r ⊕ Fin s) = Sum.inl ∘ σ := rfl
    rw [this, ← rename_rename, ← Equiv.coe_toEmbedding]
    congr 1
    exact (esymm_isSymmetric (Fin r) ℂ _) σ
  · rw [blockEsymm, rename_rename]
    have : (Sum.map σ τ ∘ Sum.inr : Fin s → Fin r ⊕ Fin s) = Sum.inr ∘ τ := rfl
    rw [this, ← rename_rename]
    congr 1
    exact (esymm_isSymmetric (Fin s) ℂ _) τ

theorem blockE_mem (f : MvPolynomial (Fin r ⊕ Fin s) ℂ) : blockE r s f ∈ symmBoth r s := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [blockE, aeval_C]
    exact (symmBoth r s).algebraMap_mem a
  | add p q hp hq =>
    rw [map_add]
    exact (symmBoth r s).add_mem hp hq
  | mul_X p v hp =>
    rw [map_mul]
    refine (symmBoth r s).mul_mem hp ?_
    rw [blockE, aeval_X]
    exact blockEsymm_mem r s v

/-! ## Through `ℂ[w][z]` -/

/-- `ℂ[w]`. -/
abbrev Tw (s : ℕ) : Type := MvPolynomial (Fin s) ℂ

/-- `β_j ↦ e_{j+1}(w)` on `ℂ[w]`. -/
def ew : Tw s →ₐ[ℂ] Tw s := aeval fun j => esymm (Fin s) ℂ ((j : ℕ) + 1)

/-- `α_j ↦ e_{j+1}(z)` on `ℂ[w][z]`, over `ℂ[w]`. -/
def ez : MvPolynomial (Fin r) (Tw s) →ₐ[Tw s] MvPolynomial (Fin r) (Tw s) :=
  aeval fun j => esymm (Fin r) (Tw s) ((j : ℕ) + 1)

theorem ew_injective : Function.Injective (ew s) := by
  intro p q h
  apply esymmAlgHom_injective ℂ (σ := Fin s) (n := s) (by simp)
  apply Subtype.ext
  rw [esymmAlgHom_apply, esymmAlgHom_apply]
  exact h

theorem ez_injective : Function.Injective (ez r s) := by
  intro p q h
  apply esymmAlgHom_injective (Tw s) (σ := Fin r) (n := r) (by simp)
  apply Subtype.ext
  rw [esymmAlgHom_apply, esymmAlgHom_apply]
  exact h

theorem ew_surjective_of_isSymmetric {p : Tw s} (hp : p.IsSymmetric) : ∃ q, ew s q = p := by
  obtain ⟨q, hq⟩ := esymmAlgHom_surjective ℂ (σ := Fin s) (n := s) (by simp) ⟨p, hp⟩
  refine ⟨q, ?_⟩
  have := congrArg Subtype.val hq
  rwa [esymmAlgHom_apply] at this

theorem ez_surjective_of_isSymmetric {p : MvPolynomial (Fin r) (Tw s)} (hp : p.IsSymmetric) :
    ∃ q, ez r s q = p := by
  obtain ⟨q, hq⟩ := esymmAlgHom_surjective (Tw s) (σ := Fin r) (n := r) (by simp) ⟨p, hp⟩
  refine ⟨q, ?_⟩
  have := congrArg Subtype.val hq
  rwa [esymmAlgHom_apply] at this

/-- `blockE` in the iterated form. -/
theorem sumAlgEquiv_blockE (f : MvPolynomial (Fin r ⊕ Fin s) ℂ) :
    sumAlgEquiv ℂ (Fin r) (Fin s) (blockE r s f) =
      ez r s (map (ew s : Tw s →+* Tw s) (sumAlgEquiv ℂ (Fin r) (Fin s) f)) := by
  have h : ((sumAlgEquiv ℂ (Fin r) (Fin s)).toAlgHom.comp (blockE r s) :
      MvPolynomial (Fin r ⊕ Fin s) ℂ →+* MvPolynomial (Fin r) (Tw s)) =
      ((ez r s : MvPolynomial (Fin r) (Tw s) →+* _).comp
        (map (ew s : Tw s →+* Tw s))).comp
        ((sumAlgEquiv ℂ (Fin r) (Fin s)).toAlgHom :
          MvPolynomial (Fin r ⊕ Fin s) ℂ →+* MvPolynomial (Fin r) (Tw s)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [blockE, ez]
    · rintro (j | j)
      · show sumAlgEquiv ℂ (Fin r) (Fin s) (blockE r s (X (Sum.inl j))) =
          ez r s (map (ew s : Tw s →+* Tw s) (sumAlgEquiv ℂ (Fin r) (Fin s) (X (Sum.inl j))))
        rw [blockE, aeval_X, blockEsymm, sumAlgEquiv_X_inl, map_X, ez, aeval_X]
        have := congrArg (fun φ : MvPolynomial (Fin r) ℂ →ₐ[ℂ] MvPolynomial (Fin r) (Tw s) =>
          φ (esymm (Fin r) ℂ ((j : ℕ) + 1)))
          (sumAlgEquiv_comp_rename_inl (R := ℂ) (S₁ := Fin r) (S₂ := Fin s))
        simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
          mapAlgHom_apply] at this
        exact this.trans (map_esymm _ _ _ _)
      · show sumAlgEquiv ℂ (Fin r) (Fin s) (blockE r s (X (Sum.inr j))) =
          ez r s (map (ew s : Tw s →+* Tw s) (sumAlgEquiv ℂ (Fin r) (Fin s) (X (Sum.inr j))))
        rw [blockE, aeval_X, blockEsymm, sumAlgEquiv_X_inr, map_C, ez, aeval_C]
        have := congrArg (fun φ : Tw s →ₐ[ℂ] MvPolynomial (Fin r) (Tw s) =>
          φ (esymm (Fin s) ℂ ((j : ℕ) + 1)))
          (sumAlgEquiv_comp_rename_inr (R := ℂ) (S₁ := Fin r) (S₂ := Fin s))
        simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
          IsScalarTower.coe_toAlgHom'] at this
        exact this.trans (by simp [ew])
  exact congrArg (fun φ : MvPolynomial (Fin r ⊕ Fin s) ℂ →+* MvPolynomial (Fin r) (Tw s) => φ f) h

/-- **`blockE` is injective** (algebraic independence in each block). -/
theorem blockE_injective : Function.Injective (blockE r s) := by
  intro f g h
  have h1 := congrArg (sumAlgEquiv ℂ (Fin r) (Fin s)) h
  rw [sumAlgEquiv_blockE, sumAlgEquiv_blockE] at h1
  have h2 := map_injective _ (ew_injective s) (ez_injective r s h1)
  exact (sumAlgEquiv ℂ (Fin r) (Fin s)).injective h2

/-- Renaming the `w`-variables of `ℂ[w]`. -/
def renW (τ : Equiv.Perm (Fin s)) : Tw s →+* Tw s := (rename (R := ℂ) (τ : Fin s → Fin s)).toRingHom

theorem sumAlgEquiv_rename_inl (σ : Equiv.Perm (Fin r)) (f : ZW r s) :
    sumAlgEquiv ℂ (Fin r) (Fin s) (rename (Sum.map σ (Equiv.refl (Fin s))) f) =
      rename (R := Tw s) (σ : Fin r → Fin r) (sumAlgEquiv ℂ (Fin r) (Fin s) f) := by
  have h : ((sumAlgEquiv ℂ (Fin r) (Fin s)).toAlgHom.comp
      (rename (Sum.map σ (Equiv.refl (Fin s)))) : ZW r s →+* MvPolynomial (Fin r) (Tw s)) =
      ((rename (R := Tw s) (σ : Fin r → Fin r)).toRingHom).comp
        ((sumAlgEquiv ℂ (Fin r) (Fin s)).toAlgHom : ZW r s →+* MvPolynomial (Fin r) (Tw s)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · rintro (j | j) <;> simp
  exact congrArg (fun φ : ZW r s →+* MvPolynomial (Fin r) (Tw s) => φ f) h

theorem sumAlgEquiv_rename_inr (τ : Equiv.Perm (Fin s)) (f : ZW r s) :
    sumAlgEquiv ℂ (Fin r) (Fin s) (rename (Sum.map (Equiv.refl (Fin r)) τ) f) =
      map (renW s τ) (sumAlgEquiv ℂ (Fin r) (Fin s) f) := by
  have h : ((sumAlgEquiv ℂ (Fin r) (Fin s)).toAlgHom.comp
      (rename (Sum.map (Equiv.refl (Fin r)) τ)) : ZW r s →+* MvPolynomial (Fin r) (Tw s)) =
      (map (renW s τ)).comp
        ((sumAlgEquiv ℂ (Fin r) (Fin s)).toAlgHom : ZW r s →+* MvPolynomial (Fin r) (Tw s)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [renW]
    · rintro (j | j) <;> simp [renW]
  exact congrArg (fun φ : ZW r s →+* MvPolynomial (Fin r) (Tw s) => φ f) h

theorem map_rename_ez (τ : Equiv.Perm (Fin s)) (h : MvPolynomial (Fin r) (Tw s)) :
    map (renW s τ) (ez r s h) = ez r s (map (renW s τ) h) := by
  have hh : (map (renW s τ)).comp
      (ez r s : MvPolynomial (Fin r) (Tw s) →+* MvPolynomial (Fin r) (Tw s)) =
      (ez r s : MvPolynomial (Fin r) (Tw s) →+* MvPolynomial (Fin r) (Tw s)).comp
        (map (renW s τ)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ez]
    · intro j
      simp [ez, map_esymm]
  exact congrArg (fun φ : MvPolynomial (Fin r) (Tw s) →+* MvPolynomial (Fin r) (Tw s) => φ h) hh

/-- **Two-block fundamental theorem**: `S_{r,s}` is the image of `blockE`. -/
theorem mem_symmBoth_iff (f : ZW r s) : f ∈ symmBoth r s ↔ ∃ g, blockE r s g = f := by
  constructor
  · intro hf
    set g := sumAlgEquiv ℂ (Fin r) (Fin s) f with hg
    have hgsymm : g.IsSymmetric := by
      intro σ
      rw [hg, ← sumAlgEquiv_rename_inl]
      congr 1
      have := hf σ (Equiv.refl (Fin s))
      exact this
    obtain ⟨h, hh⟩ := ez_surjective_of_isSymmetric r s hgsymm
    have hinv (τ : Equiv.Perm (Fin s)) : map (renW s τ) h = h := by
      apply ez_injective r s
      rw [← map_rename_ez, hh, hg, ← sumAlgEquiv_rename_inr]
      congr 1
      exact hf (Equiv.refl (Fin r)) τ
    have hcoeff : ↑h.coeffs ⊆ Set.range (ew s : Tw s →+* Tw s) := by
      intro c hc
      rw [Finset.mem_coe, mem_coeffs_iff] at hc
      obtain ⟨m, _, rfl⟩ := hc
      have hsym : (h.coeff m).IsSymmetric := by
        intro τ
        have := congrArg (fun p : MvPolynomial (Fin r) (Tw s) => p.coeff m) (hinv τ)
        simpa [coeff_map, renW] using this
      obtain ⟨q, hq⟩ := ew_surjective_of_isSymmetric s hsym
      exact ⟨q, hq⟩
    obtain ⟨h₀, hh₀⟩ := mem_range_map_iff_coeffs_subset.mpr hcoeff
    refine ⟨(sumAlgEquiv ℂ (Fin r) (Fin s)).symm h₀, ?_⟩
    apply (sumAlgEquiv ℂ (Fin r) (Fin s)).injective
    rw [sumAlgEquiv_blockE, AlgEquiv.apply_symm_apply, hh₀, hh]
  · rintro ⟨g, rfl⟩
    exact blockE_mem r s g

end KhanSL2.Depth
