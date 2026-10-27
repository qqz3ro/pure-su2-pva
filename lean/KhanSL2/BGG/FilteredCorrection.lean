module

public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Tactic.Abel

@[expose] public section

/-! Augmented exactness by correcting a Koszul primitive in successively lower filtration. -/

namespace KhanSL2.BGG.FilteredCorrection

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- A filtration-lowering perturbation of a contracted differential is augmented exact.
The submodules `P` and `Q` retain the specified chain degrees of the cycle and its primitive.
No exactness or invertibility hypothesis is assumed. -/
theorem exists_primitive_mem
    (d₀ d h : Module.End R M) (ε : M →ₗ[R] N) (i : N →ₗ[R] M)
    (F : ℕ → Submodule R M) (hF₀ : F 0 = ⊥)
    (hcover : ∀ x : M, ∃ n, x ∈ F n)
    (hpres : ∀ n, ∀ x ∈ F n, h x ∈ F n)
    (hlower : ∀ n, ∀ x ∈ F (n + 1), (d - d₀) x ∈ F n)
    (hhom : ∀ x, d₀ (h x) + h (d₀ x) = x - i (ε x))
    (hdd : ∀ x, d (d x) = 0) (hεd : ∀ x, ε (d x) = 0)
    (P Q : Submodule R M) (hPQ : ∀ x ∈ P, h x ∈ Q)
    (dQP : ∀ y ∈ Q, d y ∈ P)
    (x : M) (hxP : x ∈ P) (hcycle : d x = 0) (haug : ε x = 0) :
    ∃ y ∈ Q, d y = x := by
  obtain ⟨n, hn⟩ := hcover x
  induction n generalizing x with
  | zero =>
    have hx : x = 0 := by simpa only [hF₀, Submodule.mem_bot] using hn
    subst x
    exact ⟨0, Q.zero_mem, map_zero d⟩
  | succ n ih =>
    let δ : Module.End R M := d - d₀
    let r : M := x - d (h x)
    have hr : r = -h (δ x) - δ (h x) := by
      have hh := hhom x
      rw [haug, map_zero, sub_zero] at hh
      dsimp only [r, δ]
      simp only [LinearMap.sub_apply, map_sub, hcycle, zero_sub, map_neg, neg_neg]
      calc
        x - d (h x) = (d₀ (h x) + h (d₀ x)) - d (h x) :=
          congrArg (fun z => z - d (h x)) hh.symm
        _ = _ := by abel
    have hrF : r ∈ F n := by
      rw [hr]
      exact (F n).sub_mem ((F n).neg_mem (hpres n _ (hlower n x hn)))
        (hlower n _ (hpres (n + 1) x hn))
    have hrP : r ∈ P := P.sub_mem hxP (dQP _ (hPQ x hxP))
    have hrcycle : d r = 0 := by simp only [r, map_sub, hcycle, hdd, sub_zero]
    have hraug : ε r = 0 := by simp only [r, map_sub, haug, hεd, sub_zero]
    obtain ⟨y, hyQ, hy⟩ := ih r hrP hrcycle hraug hrF
    refine ⟨h x + y, Q.add_mem (hPQ x hxP) hyQ, ?_⟩
    rw [map_add, hy]
    dsimp only [r]
    abel

/-- The ungraded version: every cycle with zero augmentation is a boundary. -/
theorem exists_primitive
    (d₀ d h : Module.End R M) (ε : M →ₗ[R] N) (i : N →ₗ[R] M)
    (F : ℕ → Submodule R M) (hF₀ : F 0 = ⊥)
    (hcover : ∀ x : M, ∃ n, x ∈ F n)
    (hpres : ∀ n, ∀ x ∈ F n, h x ∈ F n)
    (hlower : ∀ n, ∀ x ∈ F (n + 1), (d - d₀) x ∈ F n)
    (hhom : ∀ x, d₀ (h x) + h (d₀ x) = x - i (ε x))
    (hdd : ∀ x, d (d x) = 0) (hεd : ∀ x, ε (d x) = 0)
    (x : M) (hcycle : d x = 0) (haug : ε x = 0) : ∃ y, d y = x := by
  obtain ⟨y, _, hy⟩ := exists_primitive_mem d₀ d h ε i F hF₀ hcover hpres hlower hhom
    hdd hεd ⊤ ⊤ (fun _ _ => Submodule.mem_top) (fun _ _ => Submodule.mem_top)
    x Submodule.mem_top hcycle haug
  exact ⟨y, hy⟩

end KhanSL2.BGG.FilteredCorrection
