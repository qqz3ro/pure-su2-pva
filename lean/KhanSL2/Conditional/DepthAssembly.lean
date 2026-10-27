module

public import KhanSL2.Depth.Descent

@[expose] public section

/-!
# Depth descent with a vanishing top differential

For a complex `d p : C (p + 1) → C p`, it suffices that `d c = 0`, where
`c` is the length of the regular sequence. Terms above `c` need not vanish.
All hypotheses on the comparison maps and their kernels are restricted to
`2 ≤ p ≤ c`, as is the conclusion.
-/

noncomputable section

universe u

open CategoryTheory RingTheory.Sequence

namespace KhanSL2.Conditional

open Depth

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {C : ℕ → Type u} [∀ p, AddCommGroup (C p)] [∀ p, Module R (C p)]
  {d : ∀ p, C (p + 1) →ₗ[R] C p} {rs : List R}

/-- Depth descent on the actual complex, using a zero top differential instead
of requiring the complex to vanish in all higher degrees. -/
theorem kernel_eq_zero_of_depth_of_top_zero (hrs : IsRegular R rs)
    [∀ p, Module.Finite R (C p)] [∀ p, Module.Projective R (C p)]
    (htop : d rs.length = 0)
    (hd : ∀ p, (d p).comp (d (p + 1)) = 0)
    (J : ℕ → Type u) [∀ p, AddCommGroup (J p)] [∀ p, Module R (J p)]
    (f : ∀ p, homology C d p →ₗ[R] J p)
    (hf : ∀ p, 2 ≤ p → p ≤ rs.length → Function.Surjective (f p))
    (hker : ∀ p, 2 ≤ p → p ≤ rs.length → ∃ n : ℕ,
      ∀ x ∈ LinearMap.ker (f p), ∀ a ∈ Ideal.ofList rs ^ n, a • x = 0)
    (hJ : ∀ p : ℕ, 2 ≤ p → p ≤ rs.length →
      (p : ℕ∞) ≤ (Ideal.ofList rs).depth (ModuleCat.of R (J p))) :
    ∀ p : ℕ, 2 ≤ p → p ≤ rs.length → LinearMap.ker (f p) = ⊥ := by
  set I := Ideal.ofList rs
  set c := rs.length
  have hCdepth (p : ℕ) : (c : ℕ∞) ≤ I.depth (ModuleCat.of R (C p)) :=
    length_le_depth_of_projective hrs (C p)
  have base : (c : ℕ∞) - 1 ≤ I.depth (ModuleCat.of R (coker C d c)) := by
    have hrange : LinearMap.range (d c) = ⊥ := by
      rw [show d c = 0 from htop, LinearMap.range_zero]
    rw [Ideal.depth_eq_of_linearEquiv I (Submodule.quotEquivOfEqBot _ hrange)]
    exact le_trans tsub_le_self (hCdepth c)
  have step (p : ℕ) (hp : 1 ≤ p) (hpc : p < c)
      (ih : ((p + 1 : ℕ) : ℕ∞) - 1 ≤ I.depth (ModuleCat.of R (coker C d (p + 1)))) :
      (p : ℕ∞) - 1 ≤ I.depth (ModuleCat.of R (coker C d p)) := by
    rw [enat_natCast_sub_one] at ih
    have hT : 1 ≤ I.depth (ModuleCat.of R (coker C d (p + 1))) :=
      le_trans (by exact_mod_cast hp) ih
    have hk : LinearMap.ker (f (p + 1)) = ⊥ :=
      ker_eq_bot_of_one_le_depth (f (p + 1))
        (hker (p + 1) (by omega) (by omega)) hT
    let e : homology C d (p + 1) ≃ₗ[R] J (p + 1) :=
      LinearEquiv.ofBijective (f (p + 1))
        ⟨LinearMap.ker_eq_bot.mp hk, hf (p + 1) (by omega) (by omega)⟩
    have hK : ((p + 1 : ℕ) : ℕ∞) ≤ I.depth (ModuleCat.of R (homology C d (p + 1))) := by
      rw [Ideal.depth_eq_of_linearEquiv I e]
      exact hJ (p + 1) (by omega) (by omega)
    have hIm : (p : ℕ∞) ≤ I.depth (ModuleCat.of R (LinearMap.range (d p))) := by
      refine le_trans ?_ (depth_right_ge I (exact_homologyToCoker_cokerToRange hd p)
        (homologyToCoker_injective C d (p + 1)) (cokerToRange_surjective hd p))
      refine le_inf ih ?_
      rw [← enat_natCast_sub_one p]
      exact tsub_le_tsub_right hK 1
    refine le_trans ?_ (depth_right_ge I (LinearMap.exact_subtype_mkQ (LinearMap.range (d p)))
      (Submodule.injective_subtype _) (Submodule.mkQ_surjective _))
    refine le_inf (le_trans tsub_le_self (le_trans (by exact_mod_cast hpc.le) (hCdepth p))) ?_
    exact tsub_le_tsub_right hIm 1
  have desc : ∀ k p, c - p = k → 1 ≤ p → p ≤ c →
      (p : ℕ∞) - 1 ≤ I.depth (ModuleCat.of R (coker C d p)) := by
    intro k
    induction k with
    | zero =>
      intro p hk _ hpc
      have heq : p = c := by omega
      subst p
      exact base
    | succ k ih =>
      intro p hk hp hpc
      exact step p hp (by omega) (ih (p + 1) (by omega) (by omega) (by omega))
  intro p hp hpc
  apply ker_eq_bot_of_one_le_depth (f p) (hker p hp hpc)
  have h := desc (c - p) p rfl (by omega) hpc
  refine le_trans ?_ h
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [enat_natCast_sub_one]
  exact_mod_cast (by omega : 1 ≤ q)

/-- The same descent with support on the collision locus as the explicit input.
Finite generation supplies a uniform annihilating power degree by degree. -/
theorem kernel_eq_zero_of_support_of_top_zero (hrs : IsRegular R rs)
    [∀ p, Module.Finite R (C p)] [∀ p, Module.Projective R (C p)]
    (htop : d rs.length = 0)
    (hd : ∀ p, (d p).comp (d (p + 1)) = 0)
    (J : ℕ → Type u) [∀ p, AddCommGroup (J p)] [∀ p, Module R (J p)]
    (f : ∀ p, homology C d p →ₗ[R] J p)
    (hf : ∀ p, 2 ≤ p → p ≤ rs.length → Function.Surjective (f p))
    (hsupp : ∀ p, 2 ≤ p → p ≤ rs.length →
      Module.support R (LinearMap.ker (f p)) ⊆ PrimeSpectrum.zeroLocus (Ideal.ofList rs))
    (hJ : ∀ p : ℕ, 2 ≤ p → p ≤ rs.length →
      (p : ℕ∞) ≤ (Ideal.ofList rs).depth (ModuleCat.of R (J p))) :
    ∀ p : ℕ, 2 ≤ p → p ≤ rs.length → LinearMap.ker (f p) = ⊥ := by
  refine kernel_eq_zero_of_depth_of_top_zero hrs htop hd J f hf (fun p hp hpc => ?_) hJ
  have : IsNoetherian R (C p) := isNoetherian_of_isNoetherianRing_of_finite R (C p)
  have : Module.Finite R (cycles C d p) := Module.IsNoetherian.finite R _
  have : Module.Finite R (LinearMap.ker (f p)) := Module.IsNoetherian.finite R _
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_support_subset (hsupp p hp hpc)
  exact ⟨n, fun x hx a ha => congrArg Subtype.val (hn a ha ⟨x, hx⟩)⟩

end KhanSL2.Conditional
