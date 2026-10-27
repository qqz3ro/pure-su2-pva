module

public import KhanSL2.BGG.ExteriorModel
public import KhanSL2.ExteriorDerivation
public import Mathlib.Algebra.Lie.OfAssociative

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Infinitesimal actions on the concrete exterior algebra. Linear changes of
its degree-one generators extend to ordinary derivations, and the extension
preserves Lie brackets. -/

noncomputable section
namespace KhanSL2.FiniteExterior

variable {α : Type*} [DecidableEq α] [GeneratorOrder α]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Extend an endomorphism of generator space by the ordinary Leibniz rule. -/
def infinitesimalAction (f : Module.End ℂ (α →₀ ℂ)) : Module.End ℂ (Exterior α) :=
  extendDerivation GeneratorOrder.code (fun a => generatorLinear (f (Finsupp.single a 1)))

@[simp] theorem infinitesimalAction_one (f : Module.End ℂ (α →₀ ℂ)) :
    infinitesimalAction f 1 = 0 := by
  change extendDerivation _ _ (monomial ∅) = 0
  rw [extendDerivation_monomial]
  simp

@[simp] theorem infinitesimalAction_generator (f : Module.End ℂ (α →₀ ℂ)) (a : α) :
    infinitesimalAction f (generator a) = generatorLinear (f (Finsupp.single a 1)) := by
  change extendDerivation _ _ (monomial {a}) = _
  rw [extendDerivation_monomial]
  simp [position, Finset.filter_singleton, wedge_one_right]

theorem infinitesimalAction_generatorLinear (f : Module.End ℂ (α →₀ ℂ)) (v : α →₀ ℂ) :
    infinitesimalAction f (generatorLinear v) = generatorLinear (f v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single a r =>
    rw [generatorLinear_single, map_smul, infinitesimalAction_generator]
    have hr : Finsupp.single a r = r • Finsupp.single a (1 : ℂ) := by simp
    rw [hr, map_smul, map_smul]

theorem infinitesimalAction_mul (f : Module.End ℂ (α →₀ ℂ)) (u v : Exterior α) :
    infinitesimalAction f (u * v) = infinitesimalAction f u * v + u * infinitesimalAction f v := by
  have h := extendDerivation_wedge GeneratorOrder.code GeneratorOrder.code_injective
    (fun a => generatorLinear (f (Finsupp.single a 1))) u v (1 : ℂ)
  simpa only [one_smul, infinitesimalAction, mul_def] using h (fun a => by
    simpa only [one_smul] using
      (wedge_comm_of_parity_odd GeneratorOrder.code GeneratorOrder.code_injective
        (generatorLinear (f (Finsupp.single a 1))) (parity_generatorLinear _) u).symm)

/-- Diagonal generator actions are diagonal on exterior monomials, with additive weights. -/
theorem infinitesimalAction_monomial_of_diagonal
    (f : Module.End ℂ (α →₀ ℂ)) (w : α → ℂ)
    (hf : ∀ a, f (Finsupp.single a 1) = w a • Finsupp.single a 1) (s : Finset α) :
    infinitesimalAction f (monomial s) = (∑ a ∈ s, w a) • monomial s := by
  rw [infinitesimalAction, extendDerivation_monomial, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [hf, map_smul, generatorLinear_single, one_smul, wedge_smul_left,
    wedge_generator_monomial_eq]
  simp only [Finset.notMem_erase, ↓reduceIte, position_erase_self, Finset.insert_erase ha]
  simp only [smul_smul]
  congr 1
  calc
    (-1 : ℂ) ^ position GeneratorOrder.code a s *
        (w a * (-1 : ℂ) ^ position GeneratorOrder.code a s) =
      w a * ((-1 : ℂ) ^ position GeneratorOrder.code a s *
        (-1 : ℂ) ^ position GeneratorOrder.code a s) := by ring
    _ = w a := by rw [← mul_pow]; simp
/-- Ordinary derivations are determined by their values on exterior generators. -/
theorem evenLinearMap_ext (f g : Module.End ℂ (Exterior α))
    (hf1 : f 1 = 0) (hg1 : g 1 = 0)
    (hf : ∀ u v, f (u * v) = f u * v + u * f v)
    (hg : ∀ u v, g (u * v) = g u * v + u * g v)
    (hgen : ∀ a, f (generator a) = g (generator a)) : f = g := by
  apply LinearMap.ext
  intro w
  refine induction_on GeneratorOrder.code (P := fun u => f u = g u) ?_ ?_ ?_ ?_ ?_ w
  · simp
  · exact hf1.trans hg1.symm
  · intro u v hu hv
    simp only [map_add, hu, hv]
  · intro r u hu
    simp only [map_smul, hu]
  · intro a u hu
    change f (generator a * u) = g (generator a * u)
    rw [hf, hg, hgen, hu]

/-- Commutators of ordinary derivations again obey ordinary Leibniz. -/
theorem even_commutator_mul (f g : Module.End ℂ (Exterior α))
    (hf : ∀ u v, f (u * v) = f u * v + u * f v)
    (hg : ∀ u v, g (u * v) = g u * v + u * g v) (u v : Exterior α) :
    (f * g - g * f) (u * v) =
      (f * g - g * f) u * v + u * (f * g - g * f) v := by
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hf, hg, map_add, sub_mul, mul_sub]
  abel

/-- The extension to exterior generators is linear in the given endomorphism. -/
def infinitesimalActionLinear :
    Module.End ℂ (α →₀ ℂ) →ₗ[ℂ] Module.End ℂ (Exterior α) where
  toFun := infinitesimalAction
  map_add' f g := by
    apply evenLinearMap_ext
    · simp
    · simp
    · exact infinitesimalAction_mul (f + g)
    · intro u v
      simp only [LinearMap.add_apply, infinitesimalAction_mul, add_mul, mul_add]
      abel
    · intro a
      simp
  map_smul' r f := by
    apply evenLinearMap_ext
    · simp
    · simp
    · exact infinitesimalAction_mul (r • f)
    · intro u v
      simp only [LinearMap.smul_apply, infinitesimalAction_mul, smul_add,
        smul_mul_assoc, mul_smul_comm]
    · intro a
      simp

theorem infinitesimalAction_map_lie (f g : Module.End ℂ (α →₀ ℂ)) :
    infinitesimalAction ⁅f, g⁆ = ⁅infinitesimalAction f, infinitesimalAction g⁆ := by
  change infinitesimalAction (f * g - g * f) =
    infinitesimalAction f * infinitesimalAction g - infinitesimalAction g * infinitesimalAction f
  apply evenLinearMap_ext
  · simp
  · simp
  · exact infinitesimalAction_mul _
  · exact even_commutator_mul _ _ (infinitesimalAction_mul f) (infinitesimalAction_mul g)
  · intro a
    simp only [infinitesimalAction_generator, LinearMap.sub_apply, Module.End.mul_apply,
      map_sub, infinitesimalAction_generatorLinear]

/-- The genuine Lie action of all generator-space endomorphisms on exterior algebra. -/
def infinitesimalLieMap :
    Module.End ℂ (α →₀ ℂ) →ₗ⁅ℂ⁆ Module.End ℂ (Exterior α) :=
  { infinitesimalActionLinear with map_lie' := fun {f g} => infinitesimalAction_map_lie f g }

@[simp] theorem infinitesimalLieMap_apply (f : Module.End ℂ (α →₀ ℂ)) :
    infinitesimalLieMap f = infinitesimalAction f := rfl

end KhanSL2.FiniteExterior