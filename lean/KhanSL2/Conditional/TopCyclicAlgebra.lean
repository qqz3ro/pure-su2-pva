module

public import KhanSL2.Conditional.Top

@[expose] public section

/-! # A cyclic module detected by a surjection from a submodule -/

noncomputable section
namespace KhanSL2.Conditional

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A cyclic module with a submodule surjecting onto its scalar ring is free of rank one. -/
theorem cyclic_generator_bijective_of_submodule_surjective
    (g : M) (hg : Function.Surjective (LinearMap.toSpanSingleton R M g))
    (P : Submodule R M) (f : P →ₗ[R] R) (hf : Function.Surjective f) :
    Function.Bijective (LinearMap.toSpanSingleton R M g) := by
  refine ⟨?_, hg⟩
  obtain ⟨v, hv⟩ := hf 1
  obtain ⟨a, ha⟩ := hg (v : M)
  have hz : ∀ r : R, r • g = 0 → r = 0 := by
    intro r hr
    have hrv : r • v = 0 := by
      apply Subtype.ext
      change r • (v : M) = 0
      change a • g = (v : M) at ha
      calc
        r • (v : M) = r • (a • g) := congrArg (fun x : M => r • x) ha.symm
        _ = a • (r • g) := smul_comm r a g
        _ = 0 := by rw [hr, smul_zero]
    calc
      r = r * f v := by rw [hv, mul_one]
      _ = f (r • v) := (f.map_smul r v).symm
      _ = 0 := by rw [hrv, map_zero]
  intro a b hab
  apply sub_eq_zero.mp
  apply hz
  change a • g = b • g at hab
  rw [sub_smul, hab, sub_self]

/-- The equivalence uses the specified cyclic generator and the proved submodule surjection. -/
def cyclicEquivOfSubmoduleSurjective
    (g : M) (hg : Function.Surjective (LinearMap.toSpanSingleton R M g))
    (P : Submodule R M) (f : P →ₗ[R] R) (hf : Function.Surjective f) : M ≃ₗ[R] R :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton R M g)
    (cyclic_generator_bijective_of_submodule_surjective g hg P f hf)).symm

end KhanSL2.Conditional
