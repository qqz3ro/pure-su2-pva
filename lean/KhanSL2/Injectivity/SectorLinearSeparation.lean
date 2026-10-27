module

public import KhanSL2.Injectivity.SourceSectors
public import KhanSL2.Injectivity.TaylorSeparation

@[expose] public section

noncomputable section

namespace KhanSL2.Injectivity

open Source

variable {H : Type*} [AddCommGroup H] [Module ℂ H]

theorem linear_sector_component (f : Source →ₗ[ℂ] H)
    (components : H →ₗ[ℂ] Degree →₀ H)
    (homogeneous : ∀ (t : SectorIndex) (a : Source), a ∈ indexedSector t →
      components (f a) = Finsupp.single (sectorDegree t.1 t.2.1 t.2.2) (f a))
    (v : DirectSum SectorIndex fun t => indexedSector t) (t : SectorIndex) :
    components (f (DirectSum.coeLinearMap indexedSector v))
      (sectorDegree t.1 t.2.1 t.2.2) = f (v t) := by
  classical
  induction v using DirectSum.induction_on with
  | zero => simp
  | of u a =>
    rw [DirectSum.coeLinearMap_of, homogeneous u a a.property]
    by_cases h : u = t
    · subst u
      simp
    · have hd : sectorDegree u.1 u.2.1 u.2.2 ≠ sectorDegree t.1 t.2.1 t.2.2 :=
        fun hdeg => h (sectorDegree_injective hdeg)
      simp [Finsupp.single_eq_of_ne' hd, DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
  | add a b ha hb =>
    simp only [map_add, Finsupp.add_apply, DirectSum.add_apply, Submodule.coe_add]
    rw [ha, hb]

theorem linear_injective_of_sector_kernel (f : Source →ₗ[ℂ] H)
    (components : H →ₗ[ℂ] Degree →₀ H)
    (homogeneous : ∀ (t : SectorIndex) (a : Source), a ∈ indexedSector t →
      components (f a) = Finsupp.single (sectorDegree t.1 t.2.1 t.2.2) (f a))
    (hsector : ∀ (r s N : ℕ) (a : Source), a ∈ sector r s N → f a = 0 → a = 0) :
    Function.Injective f := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro a ha
  obtain ⟨v, rfl⟩ := sector_grading_internal.surjective a
  have heq : DirectSum.coeLinearMap indexedSector v =
      DirectSum.coeAddMonoidHom indexedSector v := by
    rw [DirectSum.coeLinearMap_eq_dfinsuppSum,
      DirectSum.coeAddMonoidHom_eq_dfinsuppSum]
  rw [← heq] at ha
  have hv : v = 0 := by
    apply DFinsupp.ext
    intro t
    apply Subtype.ext
    apply hsector t.1 t.2.1 t.2.2 (v t) (v t).property
    rw [← linear_sector_component f components homogeneous v t,
      LinearMap.mem_ker.mp ha]
    simp
  simp [hv]

end KhanSL2.Injectivity
