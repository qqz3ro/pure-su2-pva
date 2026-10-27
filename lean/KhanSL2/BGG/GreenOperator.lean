module

public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

/-! The algebraic Green operator for an endomorphism with complementary kernel and range.
All splitting hypotheses are explicit; the concrete BGG application must prove them. -/
noncomputable section
namespace KhanSL2.BGG.Spectral

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- The inverse of `f` on its range. -/
def rangeEquiv (f : Module.End K M) (h : IsCompl (LinearMap.ker f) (LinearMap.range f)) :
    LinearMap.range f ≃ₗ[K] LinearMap.range f :=
  f.kerComplementEquivRange h.symm

/-- Invert on the range and kill the kernel. -/
def green (f : Module.End K M) (h : IsCompl (LinearMap.ker f) (LinearMap.range f)) :
    Module.End K M :=
  (LinearMap.range f).subtype.comp ((rangeEquiv f h).symm.toLinearMap.comp
    ((LinearMap.range f).projectionOnto (LinearMap.ker f) h.symm))

variable (f : Module.End K M) (h : IsCompl (LinearMap.ker f) (LinearMap.range f))

@[simp] theorem rangeEquiv_apply (x : LinearMap.range f) :
    (rangeEquiv f h x : M) = f x := rfl

theorem green_mem_range (x : M) : green f h x ∈ LinearMap.range f :=
  ((rangeEquiv f h).symm ((LinearMap.range f).projectionOnto (LinearMap.ker f) h.symm x)).property

theorem f_green (x : M) :
    f (green f h x) = (LinearMap.range f).projection (LinearMap.ker f) h.symm x := by
  exact congrArg (fun z : LinearMap.range f => (z : M))
    ((rangeEquiv f h).apply_symm_apply
      ((LinearMap.range f).projectionOnto (LinearMap.ker f) h.symm x))

include h in
theorem range_injective {x y : M} (hx : x ∈ LinearMap.range f) (hy : y ∈ LinearMap.range f)
    (hxy : f x = f y) : x = y := by
  have he : rangeEquiv f h ⟨x,hx⟩ = rangeEquiv f h ⟨y,hy⟩ := Subtype.ext hxy
  exact congrArg (fun z : LinearMap.range f => (z:M)) ((rangeEquiv f h).injective he)

theorem f_rangeProjection (x : M) :
    f ((LinearMap.range f).projection (LinearMap.ker f) h.symm x) = f x := by
  have hk : f ((LinearMap.ker f).projection (LinearMap.range f) h x) = 0 :=
    (LinearMap.ker f).projection_apply_mem h x
  have hs := (LinearMap.ker f).projection_add_projection_eq_self h x
  have he := congrArg f hs
  rw [map_add, hk, zero_add] at he
  exact he

theorem green_f (x : M) :
    green f h (f x) = (LinearMap.range f).projection (LinearMap.ker f) h.symm x := by
  apply range_injective f h (green_mem_range f h (f x))
    ((LinearMap.range f).projection_apply_mem h.symm x)
  rw [f_green f h, f_rangeProjection f h,
    (LinearMap.range f).projection_apply_of_mem_left h.symm (LinearMap.mem_range_self f x)]

theorem green_eq_zero_of_mem_ker {x : M} (hx : x ∈ LinearMap.ker f) : green f h x = 0 := by
  change ((rangeEquiv f h).symm ((LinearMap.range f).projectionOnto
    (LinearMap.ker f) h.symm x) : M) = 0
  rw [(LinearMap.range f).projectionOnto_apply_of_mem_right h.symm hx, map_zero]
  rfl

theorem kernelProjection_green (x : M) :
    (LinearMap.ker f).projection (LinearMap.range f) h (green f h x) = 0 :=
  (LinearMap.ker f).projection_apply_of_mem_right h (green_mem_range f h x)

theorem f_mul_green : f * green f h =
    1 - (LinearMap.ker f).projection (LinearMap.range f) h := by
  apply LinearMap.ext
  intro x
  rw [Module.End.mul_apply, f_green]
  exact (LinearMap.ker f).projection_eq_self_sub_projection h x

private theorem rangeProjection_commute (a : Module.End K M) (ha : Commute f a) :
    Commute ((LinearMap.range f).projection (LinearMap.ker f) h.symm) a := by
  apply (LinearMap.IsIdempotentElem.commute_iff
    ((LinearMap.range f).isIdempotentElem_projection h.symm)).mpr
  rw [Submodule.range_projection, Submodule.ker_projection]
  constructor
  · intro x hx
    obtain ⟨y,rfl⟩ := hx
    exact ⟨a y, LinearMap.congr_fun ha.eq y⟩
  · intro x hx
    change f (a x) = 0
    have he := LinearMap.congr_fun ha.eq x
    change f (a x) = a (f x) at he
    rw [he, LinearMap.mem_ker.mp hx, map_zero]

/-- The Green operator commutes with every endomorphism commuting with `f`. -/
theorem green_commute (a : Module.End K M) (ha : Commute f a) : Commute (green f h) a := by
  apply LinearMap.ext
  intro x
  change green f h (a x) = a (green f h x)
  have hr : a (green f h x) ∈ LinearMap.range f := by
    obtain ⟨y,hy⟩ := green_mem_range f h x
    exact ⟨a y, (LinearMap.congr_fun ha.eq y).trans (congrArg a hy)⟩
  apply range_injective f h (green_mem_range f h (a x)) hr
  rw [f_green]
  have he := LinearMap.congr_fun ha.eq (green f h x)
  change f (a (green f h x)) = a (f (green f h x)) at he
  rw [he, f_green]
  exact LinearMap.congr_fun (rangeProjection_commute f h a ha).eq x

include h in
/-- A commuting map which kills the kernel takes its values in the range. -/
theorem map_mem_range_of_kills_ker (a : Module.End K M) (ha : Commute f a)
    (hak : ∀ x, f x=0 → a x=0) (x : M) : a x ∈ LinearMap.range f := by
  have hs := (LinearMap.ker f).projection_add_projection_eq_self h x
  have hk : a ((LinearMap.ker f).projection (LinearMap.range f) h x) = 0 :=
    hak _ ((LinearMap.ker f).projection_apply_mem h x)
  have he := congrArg a hs
  rw [map_add, hk, zero_add] at he
  obtain ⟨y,hy⟩ := (LinearMap.range f).projection_apply_mem h.symm x
  exact ⟨a y, (LinearMap.congr_fun ha.eq y).trans ((congrArg a hy).trans he)⟩
end KhanSL2.BGG.Spectral