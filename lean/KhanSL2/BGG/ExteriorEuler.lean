module

public import KhanSL2.BGG.ExteriorAction
public import Mathlib.LinearAlgebra.Finsupp.Supported

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Euler operators for arbitrary weights on concrete exterior generators. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.FiniteExterior

variable {α : Type*} [DecidableEq α] [GeneratorOrder α]

def weightedGeneratorEnd (w : α → ℂ) : Module.End ℂ (α →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun a => w a • Finsupp.single a 1)

omit [DecidableEq α] [GeneratorOrder α] in
@[simp] theorem weightedGeneratorEnd_single (w : α → ℂ) (a : α) :
    weightedGeneratorEnd w (Finsupp.single a 1) = w a • Finsupp.single a 1 := by
  simp [weightedGeneratorEnd]

/-- The Euler derivation of a specified generator weighting. -/
def euler (w : α → ℂ) : Module.End ℂ (Exterior α) :=
  infinitesimalAction (weightedGeneratorEnd w)

@[simp] theorem euler_one (w : α → ℂ) : euler w 1 = 0 := infinitesimalAction_one _

@[simp] theorem euler_generator (w : α → ℂ) (a : α) :
    euler w (generator a) = w a • generator a := by
  simp [euler, infinitesimalAction_generator]

theorem euler_mul (w : α → ℂ) (u v : Exterior α) :
    euler w (u * v) = euler w u * v + u * euler w v := infinitesimalAction_mul _ _ _

theorem euler_monomial (w : α → ℂ) (s : Finset α) :
    euler w (monomial s) = (∑ a ∈ s, w a) • monomial s :=
  infinitesimalAction_monomial_of_diagonal _ w (weightedGeneratorEnd_single w) s

theorem euler_apply (w : α → ℂ) (u : Exterior α) (s : Finset α) :
    euler w u s = (∑ a ∈ s, w a) * u s := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, Finsupp.add_apply, hu, hv, mul_add]
  | single t r =>
    have hr : Finsupp.single t r = r • monomial t := by simp [monomial]
    rw [hr, map_smul, euler_monomial]
    simp only [Finsupp.smul_apply, smul_eq_mul, monomial, Finsupp.single_apply]
    by_cases h : t = s
    · subst t
      simp
      ring
    · simp [h]

/-- An Euler eigenvector has exactly the corresponding support weights. -/
theorem euler_eq_smul_iff (w : α → ℂ) (c : ℂ) (u : Exterior α) :
    euler w u = c • u ↔ ∀ s ∈ u.support, (∑ a ∈ s, w a) = c := by
  constructor
  · intro h s hs
    have heq := congrArg (fun v : Exterior α => v s) h
    rw [euler_apply, Finsupp.smul_apply, smul_eq_mul] at heq
    exact mul_right_cancel₀ (Finsupp.mem_support_iff.mp hs) heq
  · intro h
    apply Finsupp.ext
    intro s
    rw [euler_apply, Finsupp.smul_apply, smul_eq_mul]
    by_cases hs : s ∈ u.support
    · rw [h s hs]
    · have hz : u s = 0 := Finsupp.notMem_support_iff.mp hs
      simp [hz]

theorem euler_nat_eq_smul_iff (w : α → ℕ) (N : ℕ) (u : Exterior α) :
    euler (fun a => (w a : ℂ)) u = (N : ℂ) • u ↔
      ∀ s ∈ u.support, (∑ a ∈ s, w a) = N := by
  simpa only [← Nat.cast_sum, Nat.cast_inj] using
    euler_eq_smul_iff (fun a => (w a : ℂ)) (N : ℂ) u

theorem euler_degree_eq_smul_iff (d : ℕ) (u : Exterior α) :
    euler (fun _ => (1 : ℂ)) u = (d : ℂ) • u ↔ ∀ s ∈ u.support, s.card = d := by
  simpa using euler_nat_eq_smul_iff (fun _ : α => 1) d u

/-- Support degree/energy conditions are precisely two Euler eigenvalue conditions. -/
theorem mem_degree_energy_iff_euler (w : α → ℕ) (d N : ℕ) (u : Exterior α) :
    u ∈ Finsupp.supported ℂ ℂ {s : Finset α | s.card = d ∧ (∑ a ∈ s, w a) = N} ↔
      euler (fun _ => (1 : ℂ)) u = (d : ℂ) • u ∧
      euler (fun a => (w a : ℂ)) u = (N : ℂ) • u := by
  rw [euler_degree_eq_smul_iff, euler_nat_eq_smul_iff]
  constructor
  · intro hu
    exact ⟨fun s hs => (hu hs).1, fun s hs => (hu hs).2⟩
  · rintro ⟨hd, hN⟩ s hs
    exact ⟨hd s hs, hN s hs⟩

variable {β : Type*} [DecidableEq β] [GeneratorOrder β]

/-- An algebra map intertwines Euler derivations once it does so on generators. -/
theorem euler_algHom (φ : Exterior α →ₐ[ℂ] Exterior β) (w : α → ℂ) (v : β → ℂ)
    (hgen : ∀ a, euler v (φ (generator a)) = φ (w a • generator a)) (u : Exterior α) :
    euler v (φ u) = φ (euler w u) := by
  refine induction_on (GeneratorOrder.code (α := α))
    (P := fun z => euler v (φ z) = φ (euler w z)) ?_ ?_ ?_ ?_ ?_ u
  · simp
  · change euler v (φ 1) = φ (euler w 1)
    simp
  · intro y z hy hz
    simp only [map_add, hy, hz]
  · intro r z hz
    simp only [map_smul, hz]
  · intro a z hz
    change euler v (φ (generator a * z)) = φ (euler w (generator a * z))
    simp only [map_mul, euler_mul, euler_generator, map_add, hgen, hz]

end KhanSL2.FiniteExterior