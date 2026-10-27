module

public import KhanSL2.BGG.EquivariantHarmonicDecomposition

@[expose] public section

/-!
# Vanishing of standard-module tensors in diagonal coinvariants

The bottom vector of `V(n)` has weight `-n`. Surjectivity of `H - n` on
an `E`-stable coefficient subspace kills every tensor with that bottom
vector. The raising relation then kills every higher basis vector.
No finite-dimensionality or complete-reducibility assumption on the
coefficient module is needed.
-/

noncomputable section
namespace KhanSL2.BGGBridge

variable {N Q : Type*} [AddCommGroup N] [Module ℂ N]
  [AddCommGroup Q] [Module ℂ Q]

/-- A bilinear image of `V(n)` and a coefficient subspace lies in the diagonal
relations when `H-n` is surjective on that subspace and raising preserves it. -/
theorem standard_bilinear_mem_of_shift_surjective
    (n : ℕ) (P : Submodule ℂ N) (W : Submodule ℂ Q)
    (H E : Module.End ℂ N)
    (F : TauCeti.Sl2Std ℂ n →ₗ[ℂ] N →ₗ[ℂ] Q)
    (hH : ∀ v x, x ∈ P →
      F (TauCeti.Sl2Std.diag ℂ n v) x + F v (H x) ∈ W)
    (hE : ∀ v x, x ∈ P →
      F (TauCeti.Sl2Std.raise ℂ n v) x + F v (E x) ∈ W)
    (hEP : ∀ x, x ∈ P → E x ∈ P)
    (hshift : ∀ x, x ∈ P → ∃ y, y ∈ P ∧ H y - (n : ℂ) • y = x)
    (v : TauCeti.Sl2Std ℂ n) (x : N) (hx : x ∈ P) : F v x ∈ W := by
  have hbase : ∀ x, x ∈ P → F (TauCeti.Sl2Std.basisVector ℂ n n) x ∈ W := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hshift x hx
    have hm := hH (TauCeti.Sl2Std.basisVector ℂ n n) y hy
    rw [TauCeti.Sl2Std.diag_basisVector,
      show (n : ℂ) - 2 * n = -(n : ℂ) by ring] at hm
    simpa only [map_smul, LinearMap.smul_apply, LinearMap.neg_apply, LinearMap.add_apply,
      map_sub, map_add, map_neg, neg_smul,
      sub_eq_add_neg, add_comm] using hm
  have hstep (i : ℕ) (hi : i < n)
      (ih : ∀ x, x ∈ P → F (TauCeti.Sl2Std.basisVector ℂ n (i+1)) x ∈ W) :
      ∀ x, x ∈ P → F (TauCeti.Sl2Std.basisVector ℂ n i) x ∈ W := by
    intro x hx
    have hm := hE (TauCeti.Sl2Std.basisVector ℂ n (i+1)) x hx
    rw [TauCeti.Sl2Std.raise_basisVector (by omega), Nat.add_sub_cancel,
      map_smul, LinearMap.smul_apply] at hm
    have hh := W.sub_mem hm (ih (E x) (hEP x hx))
    rw [add_sub_cancel_right] at hh
    exact (W.smul_mem_iff (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i) :
      ((i+1 : ℕ) : ℂ) ≠ 0)).mp hh
  have hb (i : ℕ) (hi : i ≤ n) :
      ∀ x, x ∈ P → F (TauCeti.Sl2Std.basisVector ℂ n i) x ∈ W :=
    Nat.decreasingInduction (motive := fun i _ =>
      ∀ x, x ∈ P → F (TauCeti.Sl2Std.basisVector ℂ n i) x ∈ W)
      hstep hbase hi
  have hspan : (⊤ : Submodule ℂ (TauCeti.Sl2Std ℂ n)) ≤ W.comap (F.flip x) := by
    rw [← (TauCeti.Sl2Std.basis ℂ n).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hh := hb i.val (by omega) x hx
    rw [TauCeti.Sl2Std.basisVector_eq_basis i.isLt] at hh
    exact hh
  exact hspan (Submodule.mem_top : v ∈ (⊤ : Submodule ℂ (TauCeti.Sl2Std ℂ n)))

end KhanSL2.BGGBridge
