module

public import KhanSL2.Deformation.RestrictedActions

@[expose] public section

/-!
# Cochains in a class of modes; twisted derivations; commuting operators

* `pureIn P`: cochains built only from the modes in the class `P`. A derivation that vanishes on
  `P` kills them (`extendDerivation_pureIn_zero`), and two derivations agreeing on `P` agree on
  them (`extendDerivation_congr_pureIn`).
* `twisted_odd`, `twisted_even`: for an algebra map `F` sending generators to odd elements,
  `F ∘ D = D' ∘ F` for derivations `D, D'` follows from the generators.
* `comm_odd_even`, `comm_even_even`, `anticomm_odd_odd`: (anti)commutation of derivations
  follows from the generators; `generator_comm_of_disjoint`: derivations living on disjoint
  classes of modes commute on generators.
* `pair_sum_comm`: an operator under which two triples transform as vectors commutes with
  their contraction `Σ_a X_a Y_a`.
-/

noncomputable section

namespace KhanSL2

open Deformation

/-! ## Cochains built from a class of modes -/

/-- Cochains built from the modes in the class `P`. -/
def pureIn (P : Mode → Bool) : Submodule ℂ Cochain :=
  Finsupp.supported ℂ ℂ {t | ∀ m ∈ t, P m = true}

theorem mem_pureIn_iff {P : Mode → Bool} {u : Cochain} :
    u ∈ pureIn P ↔ ∀ t ∈ u.support, ∀ m ∈ t, P m = true :=
  Finsupp.mem_supported ℂ u

theorem single_mem_pureIn {P : Mode → Bool} {t : ExteriorMonomial} (ht : ∀ m ∈ t, P m = true)
    (r : ℂ) : Finsupp.single t r ∈ pureIn P := Finsupp.single_mem_supported ℂ r ht

theorem generator_mem_pureIn {P : Mode → Bool} {m : Mode} (hm : P m = true) :
    generator m ∈ pureIn P :=
  single_mem_pureIn (fun m' hm' => by rw [Finset.mem_singleton.mp hm']; exact hm) 1

theorem one_mem_pureIn (P : Mode → Bool) : cochainOne ∈ pureIn P :=
  single_mem_pureIn (fun m hm => absurd hm (Finset.notMem_empty m)) 1

theorem mul_mem_pureIn {P : Mode → Bool} {u v : Cochain} (hu : u ∈ pureIn P)
    (hv : v ∈ pureIn P) : u * v ∈ pureIn P := by
  rw [cochain_mul_eq_wedge, ← u.sum_single, ← v.sum_single]
  simp only [Finsupp.sum, wedge, map_sum, LinearMap.sum_apply]
  apply (pureIn P).sum_mem
  intro t ht
  apply (pureIn P).sum_mem
  intro s hs
  simp only [wedgeLinear, Finsupp.linearCombination_single, LinearMap.smul_apply, smul_smul]
  apply (pureIn P).smul_mem
  unfold monomialWedge
  split
  · apply single_mem_pureIn
    intro m hm
    rcases Finset.mem_union.mp hm with h | h
    · exact (mem_pureIn_iff.mp hu) s hs m h
    · exact (mem_pureIn_iff.mp hv) t ht m h
  · exact (pureIn P).zero_mem

theorem extendDerivation_zero_fun : extendDerivation (fun _ => (0 : Cochain)) = 0 := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  simp [extendDerivation, wedge]

theorem extendDerivation_single_congr (f f' : Mode → Cochain) {t : ExteriorMonomial}
    (h : ∀ m ∈ t, f m = f' m) (r : ℂ) :
    extendDerivation f (Finsupp.single t r) = extendDerivation f' (Finsupp.single t r) := by
  simp only [extendDerivation, Finsupp.linearCombination_single]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [h m hm]

/-- Derivations agreeing on the modes of `P` agree on `P`-cochains. -/
theorem extendDerivation_congr_pureIn {P : Mode → Bool} (f f' : Mode → Cochain)
    (h : ∀ m, P m = true → f m = f' m) {u : Cochain} (hu : u ∈ pureIn P) :
    extendDerivation f u = extendDerivation f' u := by
  rw [← u.sum_single]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact extendDerivation_single_congr f f' (fun m hm => h m (mem_pureIn_iff.mp hu t ht m hm)) _

/-- A derivation vanishing on the modes of `P` kills `P`-cochains. -/
theorem extendDerivation_pureIn_zero {P : Mode → Bool} (f : Mode → Cochain)
    (h : ∀ m, P m = true → f m = 0) {u : Cochain} (hu : u ∈ pureIn P) :
    extendDerivation f u = 0 := by
  rw [extendDerivation_congr_pureIn f (fun _ => 0) h hu, extendDerivation_zero_fun,
    LinearMap.zero_apply]

/-- A derivation with `P`-valued generator images on `P` preserves `P`-cochains. -/
theorem extendDerivation_mem_pureIn {P : Mode → Bool} (f : Mode → Cochain)
    (h : ∀ m, P m = true → f m ∈ pureIn P) {u : Cochain} (hu : u ∈ pureIn P) :
    extendDerivation f u ∈ pureIn P := by
  rw [← u.sum_single]
  simp only [Finsupp.sum, map_sum, extendDerivation, Finsupp.linearCombination_single]
  apply (pureIn P).sum_mem
  intro t ht
  apply (pureIn P).smul_mem
  apply (pureIn P).sum_mem
  intro m hm
  apply (pureIn P).smul_mem
  have htP := mem_pureIn_iff.mp hu t ht
  rw [← cochain_mul_eq_wedge]
  exact mul_mem_pureIn (h m (htP m hm))
    (single_mem_pureIn (fun m' hm' => htP m' (Finset.mem_of_mem_erase hm')) 1)

theorem colorGenerator_mem_pureIn {P : Mode → Bool} (hP : ColorStable P) (e : Fin 3) {m : Mode}
    (hm : P m = true) : colorGenerator e m ∈ pureIn P := by
  apply (pureIn P).sum_mem
  intro c _
  exact (pureIn P).smul_mem _ (generator_mem_pureIn (by rw [hP]; exact hm))

theorem colorActionOn_mem_pureIn {P Q : Mode → Bool} (hQ : ColorStable Q) (e : Fin 3) {u : Cochain}
    (hu : u ∈ pureIn Q) : colorActionOn P e u ∈ pureIn Q :=
  extendDerivation_mem_pureIn _ (fun m hm => by
    split_ifs
    · exact colorGenerator_mem_pureIn hQ e hm
    · exact (pureIn Q).zero_mem) hu

/-! ## Twisted derivations -/

theorem twisted_odd (F : Cochain →ₐ[ℂ] Cochain)
    (hF : ∀ m, cochainParity (F (generator m)) = -F (generator m))
    {D D' : Cochain →ₗ[ℂ] Cochain} (hD : IsOddDer D) (hD' : IsOddDer D')
    (h : ∀ m, F (D (generator m)) = D' (F (generator m))) (u : Cochain) :
    F (D u) = D' (F u) := by
  have := cochain_linearMap_ext (X := F.toLinearMap ∘ₗ D) (Y := D' ∘ₗ F.toLinearMap)
    (by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, hD.map_one]
      rw [← cochain_one_eq, map_one, cochain_one_eq, hD'.map_one, map_zero])
    (fun m u hu => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at hu ⊢
      rw [hD.mul, map_mul, map_add, map_mul, map_mul, hD'.mul, hF, hu, h, cochainParity_generator,
        map_neg])
  exact LinearMap.congr_fun this u

theorem twisted_even (F : Cochain →ₐ[ℂ] Cochain)
    {E E' : Cochain →ₗ[ℂ] Cochain} (hE : IsEvenDer E) (hE' : IsEvenDer E')
    (h : ∀ m, F (E (generator m)) = E' (F (generator m))) (u : Cochain) :
    F (E u) = E' (F u) := by
  have := cochain_linearMap_ext (X := F.toLinearMap ∘ₗ E) (Y := E' ∘ₗ F.toLinearMap)
    (by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, hE.map_one]
      rw [← cochain_one_eq, map_one, cochain_one_eq, hE'.map_one, map_zero])
    (fun m u hu => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at hu ⊢
      rw [hE.mul, map_mul, map_add, map_mul, map_mul, hE'.mul, hu, h])
  exact LinearMap.congr_fun this u

/-! ## Commuting derivations -/

theorem isOddDer_zero : IsOddDer (0 : Cochain →ₗ[ℂ] Cochain) := ⟨fun _ _ => by simp, fun _ => by simp⟩

theorem isEvenDer_zero : IsEvenDer (0 : Cochain →ₗ[ℂ] Cochain) := ⟨fun _ _ => by simp, fun _ => by simp⟩

/-- An odd and an even derivation commute if they commute on generators. -/
theorem comm_odd_even {D E : Cochain →ₗ[ℂ] Cochain} (hD : IsOddDer D) (hE : IsEvenDer E)
    (h : ∀ m, D (E (generator m)) = E (D (generator m))) (v : Cochain) : D (E v) = E (D v) := by
  have := (hD.commutator hE).ext isOddDer_zero (fun m => by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply, h, sub_self])
  have h2 := LinearMap.congr_fun this v
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply] at h2
  exact sub_eq_zero.mp h2

/-- Two even derivations commute if they commute on generators. -/
theorem comm_even_even {E E' : Cochain →ₗ[ℂ] Cochain} (hE : IsEvenDer E) (hE' : IsEvenDer E')
    (h : ∀ m, E (E' (generator m)) = E' (E (generator m))) (v : Cochain) :
    E (E' v) = E' (E v) := by
  have := (hE.commutator hE').ext isEvenDer_zero (fun m => by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply, h, sub_self])
  have h2 := LinearMap.congr_fun this v
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply] at h2
  exact sub_eq_zero.mp h2

/-- Two odd derivations anticommute if they anticommute on generators. -/
theorem anticomm_odd_odd {D D' : Cochain →ₗ[ℂ] Cochain} (hD : IsOddDer D) (hD' : IsOddDer D')
    (h : ∀ m, D (D' (generator m)) + D' (D (generator m)) = 0) (v : Cochain) :
    D (D' v) + D' (D v) = 0 := by
  have := (hD.anticommutator hD').ext isEvenDer_zero (fun m => by
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply, h])
  have h2 := LinearMap.congr_fun this v
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] using h2

/-- Generator values of derivations living on disjoint classes of modes commute. -/
theorem generator_comm_of_disjoint {P Q : Mode → Bool} (hPQ : ∀ m, P m = true → Q m = false)
    (f f' : Mode → Cochain)
    (hf : ∀ m, P m = false → f m = 0) (hfP : ∀ m, P m = true → f m ∈ pureIn P)
    (hf' : ∀ m, Q m = false → f' m = 0) (hf'Q : ∀ m, Q m = true → f' m ∈ pureIn Q) (m : Mode) :
    extendDerivation f (extendDerivation f' (generator m)) =
      extendDerivation f' (extendDerivation f (generator m)) := by
  rw [extendDerivation_generator, extendDerivation_generator]
  cases hP : P m
  · cases hQ : Q m
    · rw [hf m hP, hf' m hQ, map_zero, map_zero]
    · rw [hf m hP, map_zero]
      exact extendDerivation_pureIn_zero f (fun m' hm' => by
        cases hPm : P m'
        · exact hf m' hPm
        · exact absurd (hPQ m' hPm) (by rw [hm']; simp)) (hf'Q m hQ)
  · rw [hf' m (hPQ m hP), map_zero]
    exact (extendDerivation_pureIn_zero f' (fun m' hm' => hf' m' (hPQ m' hm')) (hfP m hP)).symm

/-! ## Contractions of vectors -/

/-- If `X_a` and `Y_a` transform as vectors under `M`, then `M` commutes with `Σ_a X_a Y_a`. -/
theorem pair_sum_comm {V : Type*} [AddCommGroup V] [Module ℂ V] (M : V →ₗ[ℂ] V) (j : Fin 3)
    (X Y : Fin 3 → V →ₗ[ℂ] V)
    (hX : ∀ a v, M (X a v) - X a (M v) = ∑ d : Fin 3, epsilon j a d • X d v)
    (hY : ∀ a v, M (Y a v) - Y a (M v) = ∑ d : Fin 3, epsilon j a d • Y d v) (v : V) :
    M (∑ a : Fin 3, X a (Y a v)) = ∑ a : Fin 3, X a (Y a (M v)) := by
  have hstep (a : Fin 3) : M (X a (Y a v)) = X a (Y a (M v)) +
      (∑ d : Fin 3, epsilon j a d • X a (Y d v) + ∑ d : Fin 3, epsilon j a d • X d (Y a v)) := by
    have h1 := hX a (Y a v)
    have h2 := hY a v
    rw [sub_eq_iff_eq_add] at h1 h2
    rw [h1, h2, map_add, map_sum]
    simp only [map_smul]
    abel
  rw [map_sum, Finset.sum_congr rfl (fun a _ => hstep a), Finset.sum_add_distrib]
  conv_rhs => rw [← add_zero (∑ a : Fin 3, X a (Y a (M v)))]
  congr 1
  rw [Finset.sum_add_distrib]
  rw [show (∑ a : Fin 3, ∑ d : Fin 3, epsilon j a d • X d (Y a v)) =
      ∑ a : Fin 3, ∑ d : Fin 3, epsilon j d a • X a (Y d v) from Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro d _
  rw [epsilon_swap_right j d a, neg_smul, add_neg_cancel]

end KhanSL2
