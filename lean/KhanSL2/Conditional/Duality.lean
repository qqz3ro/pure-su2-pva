module

public import KhanSL2.Modules.SourceDualModel
public import KhanSL2.InjectivityMainStatement

@[expose] public section

/-!
# Returning from the polynomial comparison to the specified map

Injectivity of the actual comparison maps implies surjectivity of the original
`phi`. The argument uses finite-dimensional duality on each spin piece and
then the proved internal grading of restricted relative cohomology.

The hypotheses in this file are explicit conditional inputs, not axioms.
-/

noncomputable section
set_option maxHeartbeats 1000000

namespace KhanSL2.Conditional

open Current Modules

/-- The transpose of the degreewise canonical map is exactly `psiK`. -/
theorem phiPiece_dictionary_flip (p B : ℕ) (S : ℤ) :
    ((dictionary p B S).toLinearMap.comp (phiPiece (kDegree p B S))).flip =
      psiK p B S := by
  apply LinearMap.ext
  intro k
  apply LinearMap.ext
  intro a
  exact (psiK_apply p B S k a).symm

/-- Injectivity of the actual transpose gives surjectivity in its degree. -/
theorem phiPiece_surjective_of_psiK_injective (p B : ℕ) (S : ℤ)
    (h : Function.Injective (psiK p B S)) :
    Function.Surjective (phiPiece (kDegree p B S)) := by
  have hf : Function.Surjective
      ((dictionary p B S).toLinearMap.comp (phiPiece (kDegree p B S))) := by
    apply LinearMap.flip_injective_iff₂.mp
    rwa [phiPiece_dictionary_flip]
  intro y
  obtain ⟨a, ha⟩ := hf (dictionary p B S y)
  exact ⟨a, (dictionary p B S).injective ha⟩

/-- Each spin summand embeds into the algebraic direct sum. -/
theorem psiK_injective_of_psiTotal_injective (B p : ℕ)
    (h : Function.Injective (psiTotal B p)) (S : ℤ) :
    Function.Injective (psiK p B S) := by
  exact (DirectSum.lmap_injective (fun T : ℤ => psiK p B T)).mp h S

/-- The source-dual equivalence identifies the kernel of the actual polynomial
comparison with the kernel of the actual direct sum of transposes. -/
theorem psiTotal_injective_of_psiB_injective (B p : ℕ)
    (h : Function.Injective (psiB B p)) : Function.Injective (psiTotal B p) := by
  intro x y hxy
  apply h
  calc
    psiB B p x = sourceDualEquiv B p (psiTotal B p x) :=
      LinearMap.congr_fun (psiB_eq_sourceDualEquiv_comp_psiTotal B p) x
    _ = sourceDualEquiv B p (psiTotal B p y) := congrArg (sourceDualEquiv B p) hxy
    _ = psiB B p y :=
      (LinearMap.congr_fun (psiB_eq_sourceDualEquiv_comp_psiTotal B p) y).symm

/-- Every exterior monomial has a natural coefficient degree and form degree. -/
theorem monomialDegree_eq_kDegree (s : ExteriorMonomial) :
    ∃ p B : ℕ, ∃ S : ℤ, monomialDegree s = kDegree p B S := by
  have hb : ∑ m ∈ s, m.bCount ≤ s.card := by
    calc
      ∑ m ∈ s, m.bCount ≤ ∑ _m ∈ s, 1 := by
        apply Finset.sum_le_sum
        intro m _
        cases m <;> simp [Mode.bCount]
      _ = s.card := by simp
  refine ⟨s.card - ∑ m ∈ s, m.bCount, ∑ m ∈ s, m.bCount,
    (∑ m ∈ s, m.weight : ℕ), ?_⟩
  simp only [monomialDegree, kDegree, Nat.add_sub_of_le hb]

/-- A degree unsupported by any exterior monomial contributes zero cohomology. -/
theorem cohomologyPiece_eq_bot_of_unsupported (d : Degree)
    (h : ¬∃ s : ExteriorMonomial, monomialDegree s = d) :
    cohomologyPiece d = ⊥ := by
  apply le_antisymm ?_ bot_le
  rintro y ⟨u, hu, rfl⟩
  have hu0 : (u : Cochain) = 0 := by
    ext s
    exact apply_eq_zero_of_mem_piece hu (fun hs => h ⟨s, hs⟩)
  have hz : u = 0 := Subtype.ext hu0
  simp [hz]

/-- Piecewise transpose injectivity covers every degree of the restricted
cohomology; degrees outside natural form/coefficient degrees vanish. -/
theorem phiPiece_surjective_of_all_psiK_injective
    (h : ∀ (p B : ℕ) (S : ℤ), Function.Injective (psiK p B S)) (d : Degree) :
    Function.Surjective (phiPiece d) := by
  classical
  by_cases hs : ∃ s : ExteriorMonomial, monomialDegree s = d
  · obtain ⟨s, rfl⟩ := hs
    obtain ⟨p, B, S, hd⟩ := monomialDegree_eq_kDegree s
    rw [hd]
    exact phiPiece_surjective_of_psiK_injective p B S (h p B S)
  · let : Subsingleton (cohomologyPiece d) :=
      Submodule.subsingleton_iff_eq_bot.mpr (cohomologyPiece_eq_bot_of_unsupported d hs)
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩

/-- Homogeneous surjectivity assembles by the proved internal grading. -/
theorem phi_surjective_of_phiPiece_surjective
    (h : ∀ d : Degree, Function.Surjective (phiPiece d)) :
    Function.Surjective phi := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← cohomology_grading_internal.submodule_iSup_eq_top]
  apply iSup_le
  intro d y hy
  obtain ⟨a, ha⟩ := h d ⟨y, hy⟩
  exact ⟨a, congrArg Subtype.val ha⟩

/-- Conditional surjectivity of the original specified map from all actual
spinwise homology comparisons. -/
theorem phi_surjective_of_psiK_injective
    (h : ∀ (p B : ℕ) (S : ℤ), Function.Injective (psiK p B S)) :
    Function.Surjective phi :=
  phi_surjective_of_phiPiece_surjective (phiPiece_surjective_of_all_psiK_injective h)

theorem phi_surjective_of_psiTotal_injective
    (h : ∀ B p : ℕ, Function.Injective (psiTotal B p)) :
    Function.Surjective phi :=
  phi_surjective_of_psiK_injective
    (fun p B S => psiK_injective_of_psiTotal_injective B p (h B p) S)

theorem phi_surjective_of_psiB_injective
    (h : ∀ B p : ℕ, Function.Injective (psiB B p)) : Function.Surjective phi :=
  phi_surjective_of_psiTotal_injective
    (fun B p => psiTotal_injective_of_psiB_injective B p (h B p))

/-- The final PVA-isomorphism proposition for the original specified `phi`,
conditional only on injectivity of the actual polynomial comparison. -/
theorem mainStatement_of_psiB_injective
    (h : ∀ B p : ℕ, Function.Injective (psiB B p)) : MainStatement :=
  mainStatement_iff_surjective.mpr (phi_surjective_of_psiB_injective h)

end KhanSL2.Conditional

