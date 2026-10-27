module

public import TauCeti.Algebra.Homology.Contraction.Linear

@[expose] public section
namespace KhanSL2.BGG

variable {R M N Z : Type*} [Semiring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {dM : Module.End R M} {dN : Module.End R N}

/-- A contraction transfers augmented exactness with specified cycle and
primitive degrees. The augmentation need not be linear over the coefficient ring. -/
theorem contraction_augmented_exactness_mem (c : TauCeti.LinearSpecialContraction dM dN)
    (ε : M → Z) (z : Z) (PM QM : Set M) (PN QN : Set N)
    (hi : ∀ x∈PN, c.incl x∈PM) (hp : ∀ y∈QM, c.proj y∈QN)
    (hex : ∀ x∈PM, dM x=0 → ε x=z → ∃ y∈QM, dM y=x)
    (x : N) (hxmem : x∈PN) (hx : dN x=0) (hε : ε (c.incl x)=z) :
    ∃ y∈QN, dN y=x := by
  obtain ⟨y, hymem, hy⟩ := hex (c.incl x) (hi x hxmem)
    (by rw [c.dM_incl_apply, hx, map_zero]) hε
  exact ⟨c.proj y, hp y hymem, by rw [← c.proj_dM_apply, hy, c.proj_incl_apply]⟩

/-- An additive augmentation annihilating boundaries descends along the
contraction and retains any cycle section. -/
theorem contraction_augmentation_section_additive [AddCommGroup Z]
    (c : TauCeti.LinearSpecialContraction dM dN) (ε : M →+ Z) (η : Z → M)
    (hεd : ∀ x, ε (dM x)=0) (hdη : ∀ z, dM (η z)=0) (hεη : ∀ z, ε (η z)=z)
    (z : Z) : ε (c.incl (c.proj (η z))) = z := by
  rw [c.incl_proj_apply]
  simp only [map_sub, hεd, hdη, map_zero, hεη, sub_zero]

end KhanSL2.BGG