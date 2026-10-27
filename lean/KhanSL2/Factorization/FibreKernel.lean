module

public import KhanSL2.Factorization.FibreSurjectivity
public import Mathlib.Algebra.Module.Projective

@[expose] public section
noncomputable section
open TensorProduct
namespace KhanSL2.Factorization.FibreExactness

variable {R : Type*} [CommRing R]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A splitting onto the image gives an explicit retraction onto the kernel. -/
def kernelRetraction (f : M →ₗ[R] N)
    (s : LinearMap.range f →ₗ[R] M) (hs : f.rangeRestrict.comp s = LinearMap.id) :
    M →ₗ[R] LinearMap.ker f :=
  (LinearMap.id - s.comp f.rangeRestrict).codRestrict (LinearMap.ker f) (by
    intro x
    change f (x - s (f.rangeRestrict x)) = 0
    rw [map_sub]
    have hx := congrArg Subtype.val (LinearMap.congr_fun hs (f.rangeRestrict x))
    change f (s (f.rangeRestrict x)) = f x at hx
    rw [hx,sub_self])

theorem kernelRetraction_comp (f : M →ₗ[R] N)
    (s : LinearMap.range f →ₗ[R] M) (hs : f.rangeRestrict.comp s = LinearMap.id) :
    (kernelRetraction f s hs).comp (LinearMap.ker f).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (x : M) - s (f.rangeRestrict x) = x
  have hx : f.rangeRestrict x = 0 := Subtype.ext x.property
  rw [hx,map_zero,sub_zero]

theorem kernelRetraction_surjective (f : M →ₗ[R] N)
    (s : LinearMap.range f →ₗ[R] M) (hs : f.rangeRestrict.comp s = LinearMap.id) :
    Function.Surjective (kernelRetraction f s hs) := by
  intro x
  exact ⟨x,LinearMap.congr_fun (kernelRetraction_comp f s hs) x⟩

theorem kernel_finite_of_projective_range [Module.Finite R M]
    (f : M →ₗ[R] N) [Module.Projective R (LinearMap.range f)] :
    Module.Finite R (LinearMap.ker f) := by
  obtain ⟨s,hs⟩ := Module.projective_lifting_property f.rangeRestrict LinearMap.id
    f.surjective_rangeRestrict
  exact Module.Finite.of_surjective (kernelRetraction f s hs)
    (kernelRetraction_surjective f s hs)

theorem kernel_projective_of_projective_range [Module.Projective R M]
    (f : M →ₗ[R] N) [Module.Projective R (LinearMap.range f)] :
    Module.Projective R (LinearMap.ker f) := by
  obtain ⟨s,hs⟩ := Module.projective_lifting_property f.rangeRestrict LinearMap.id
    f.surjective_rangeRestrict
  exact Module.Projective.of_split (LinearMap.ker f).subtype
    (kernelRetraction f s hs) (kernelRetraction_comp f s hs)

/-- Kernel inclusion remains injective after arbitrary tensor product because
its cokernel is projective and the sequence is split. -/
theorem kernel_lTensor_injective_of_projective_range (f : M →ₗ[R] N)
    [Module.Projective R (LinearMap.range f)] (S : Type*) [AddCommGroup S] [Module R S] :
    Function.Injective ((LinearMap.ker f).subtype.lTensor S) := by
  obtain ⟨s,hs⟩ := Module.projective_lifting_property f.rangeRestrict LinearMap.id
    f.surjective_rangeRestrict
  have hcomp : ((kernelRetraction f s hs).lTensor S).comp
      ((LinearMap.ker f).subtype.lTensor S) = LinearMap.id := by
    rw [← LinearMap.lTensor_comp,kernelRetraction_comp,LinearMap.lTensor_id]
  exact Function.LeftInverse.injective (fun x => LinearMap.congr_fun hcomp x)

variable {L : Type*} [AddCommGroup L] [Module R L]

def toKernel (f : M →ₗ[R] N) (g : L →ₗ[R] M) (hfg : f.comp g = 0) :
    L →ₗ[R] LinearMap.ker f :=
  g.codRestrict (LinearMap.ker f) (fun x => LinearMap.congr_fun hfg x)

@[simp] theorem subtype_comp_toKernel (f : M →ₗ[R] N) (g : L →ₗ[R] M)
    (hfg : f.comp g = 0) :
    (LinearMap.ker f).subtype.comp (toKernel f g hfg) = g := rfl

/-- Exactness on residue fibres lifts when the preceding image is projective.
The induction applying this lemma establishes that projectivity itself. -/
theorem exact_of_maximal_fibres_of_projective_range [Module.Finite R M]
    (f : M →ₗ[R] N) (g : L →ₗ[R] M) (hfg : f.comp g = 0)
    [Module.Projective R (LinearMap.range f)]
    (h : ∀ (p : Ideal R) [p.IsMaximal],
      Function.Exact (g.lTensor p.ResidueField) (f.lTensor p.ResidueField)) :
    Function.Exact g f := by
  let := kernel_finite_of_projective_range f
  have hg : Function.Surjective (toKernel f g hfg) := by
    apply surjective_of_maximal_fibres
    intro p hp
    let := hp
    intro x
    have hx : f.lTensor p.ResidueField ((LinearMap.ker f).subtype.lTensor p.ResidueField x) = 0 := by
      rw [← LinearMap.comp_apply,← LinearMap.lTensor_comp]
      have hf : f.comp (LinearMap.ker f).subtype = 0 := by ext y; exact y.property
      rw [hf,LinearMap.lTensor_zero,LinearMap.zero_apply]
    obtain ⟨y,hy⟩ := (h p _).mp hx
    refine ⟨y,?_⟩
    apply kernel_lTensor_injective_of_projective_range f p.ResidueField
    rw [← LinearMap.comp_apply,← LinearMap.lTensor_comp,subtype_comp_toKernel]
    exact hy
  intro x
  constructor
  · intro hx
    obtain ⟨y,hy⟩ := hg ⟨x,hx⟩
    exact ⟨y,congrArg Subtype.val hy⟩
  · rintro ⟨y,rfl⟩
    exact LinearMap.congr_fun hfg y

end KhanSL2.Factorization.FibreExactness
