module

public import KhanSL2.BGG.TermResolutionEnergy

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KhanSL2.BGG.TermResolution

/-- Projection onto one of the actual quotient energy pieces, included back in its term. -/
def energyProjection (p : ℕ) (n : ℤ) : Module.End ℂ (Term p) :=
  (termPiece p n).subtype.comp
    (TauCeti.internalProjection (termPiece_independent p) (iSup_termPiece_eq_top p) n)

theorem energyProjection_mem (p : ℕ) (n : ℤ) (u : Term p) :
    energyProjection p n u ∈ termPiece p n :=
  (TauCeti.internalProjection (termPiece_independent p) (iSup_termPiece_eq_top p) n u).property

theorem energyProjection_of_mem (p : ℕ) {n : ℤ} {u : Term p}
    (hu : u ∈ termPiece p n) : energyProjection p n u = u := by
  exact congrArg (fun z : termPiece p n => (z : Term p))
    (TauCeti.internalProjection_apply_of_mem (termPiece_independent p) (iSup_termPiece_eq_top p) hu)

theorem energyProjection_of_mem_ne (p : ℕ) {m n : ℤ} {u : Term p}
    (hu : u ∈ termPiece p m) (hmn : m ≠ n) : energyProjection p n u = 0 := by
  exact congrArg (fun z : termPiece p n => (z : Term p))
    (TauCeti.internalProjection_apply_eq_zero_of_mem_of_ne
      (termPiece_independent p) (iSup_termPiece_eq_top p) hmn hu)

/-- The specified BGG differential commutes with actual homogeneous projection. -/
theorem differential_energyProjection (p : ℕ) (n : ℤ) (u : Term (p+1)) :
    differential p (energyProjection (p+1) n u) = energyProjection p n (differential p u) := by
  have hu : u ∈ ⨆ m, termPiece (p+1) m := by rw [iSup_termPiece_eq_top]; trivial
  induction hu using Submodule.iSup_induction' with
  | mem m u hu =>
    by_cases hmn : m = n
    · subst m
      rw [energyProjection_of_mem _ hu,
        energyProjection_of_mem _ (differential_mem_termPiece p hu)]
    · rw [energyProjection_of_mem_ne _ hu hmn, map_zero,
        energyProjection_of_mem_ne _ (differential_mem_termPiece p hu) hmn]
  | zero => simp
  | add u v _ _ hu hv => simp only [map_add, hu, hv]

/-- Projection to energy zero preserves the actual augmentation. -/
theorem augmentation_energyProjection_zero (u : Term 0) :
    augmentation (energyProjection 0 0 u) = augmentation u := by
  have hu : u ∈ ⨆ m, termPiece 0 m := by rw [iSup_termPiece_eq_top]; trivial
  induction hu using Submodule.iSup_induction' with
  | mem m u hu =>
    by_cases hm : m = 0
    · subst m
      rw [energyProjection_of_mem _ hu]
    · rw [energyProjection_of_mem_ne _ hu hm, map_zero,
        augmentation_eq_zero_of_energy_ne_zero hu hm]
  | zero => simp
  | add u v _ _ hu hv => simp only [map_add, hu, hv]

/-- Every positive-degree cycle of fixed physical energy has a primitive of the same energy. -/
theorem exactness_positive_degree_energy (p : ℕ) (n : ℤ) (u : Term (p+1))
    (hn : u ∈ termPiece (p+1) n) (hu : differential p u = 0) :
    ∃ v ∈ termPiece (p+2) n, differential (p+1) v = u := by
  obtain ⟨v, hv⟩ := (exact_differentials p u).mp hu
  refine ⟨energyProjection (p+2) n v, energyProjection_mem _ _ _, ?_⟩
  rw [differential_energyProjection, hv, energyProjection_of_mem _ hn]

/-- Exactness at the augmentation also holds separately in each actual energy. -/
theorem exactness_zero_degree_energy (n : ℤ) (u : Term 0)
    (hn : u ∈ termPiece 0 n) (hu : augmentation u = 0) :
    ∃ v ∈ termPiece 1 n, differential 0 v = u := by
  obtain ⟨v, hv⟩ := (exact_differential_augmentation u).mp hu
  refine ⟨energyProjection 1 n v, energyProjection_mem _ _ _, ?_⟩
  rw [differential_energyProjection, hv, energyProjection_of_mem _ hn]

/-- The scalar augmentation is already surjective on the energy-zero component. -/
theorem augmentation_surjective_energy_zero (r : ℂ) :
    ∃ u ∈ termPiece 0 0, augmentation u = r := by
  obtain ⟨u, hu⟩ := augmentation_surjective r
  exact ⟨energyProjection 0 0 u, energyProjection_mem _ _ _,
    (augmentation_energyProjection_zero u).trans hu⟩

/-- The actual BGG map restricted to one physical-energy subcomplex. -/
def energyDifferential (p : ℕ) (n : ℤ) : termPiece (p+1) n →ₗ[ℂ] termPiece p n where
  toFun u := ⟨differential p u, differential_mem_termPiece p u.property⟩
  map_add' u v := Subtype.ext ((differential p).map_add u v)
  map_smul' r u := Subtype.ext (LinearMap.map_smul_of_tower (differential p) r u)

/-- The restriction of the specified augmentation to one energy component. -/
def energyAugmentation (n : ℤ) : termPiece 0 n →ₗ[ℂ] ℂ := augmentation.comp (termPiece 0 n).subtype

/-- The genuine fixed-energy subcomplex is exact at each positive degree. -/
theorem exact_energyDifferentials (p : ℕ) (n : ℤ) :
    Function.Exact (energyDifferential (p+1) n) (energyDifferential p n) := by
  intro u
  constructor
  · intro hu
    have hu' : differential p u = 0 := congrArg Subtype.val hu
    obtain ⟨v, hv, hd⟩ := exactness_positive_degree_energy p n u u.property hu'
    exact ⟨⟨v, hv⟩, Subtype.ext hd⟩
  · rintro ⟨v, rfl⟩
    exact Subtype.ext (differential_square_zero p v)

/-- The genuine fixed-energy subcomplex is exact at degree zero. -/
theorem exact_energyDifferential_augmentation (n : ℤ) :
    Function.Exact (energyDifferential 0 n) (energyAugmentation n) := by
  intro u
  constructor
  · intro hu
    obtain ⟨v, hv, hd⟩ := exactness_zero_degree_energy n u u.property hu
    exact ⟨⟨v, hv⟩, Subtype.ext hd⟩
  · rintro ⟨v, rfl⟩
    exact augmentation_differential v

theorem energyAugmentation_zero_surjective : Function.Surjective (energyAugmentation 0) := by
  intro r
  obtain ⟨u, hu, hε⟩ := augmentation_surjective_energy_zero r
  exact ⟨⟨u, hu⟩, hε⟩

end KhanSL2.BGG.TermResolution
