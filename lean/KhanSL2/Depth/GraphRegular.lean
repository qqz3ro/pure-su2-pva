module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section

/-!
# Graph coordinates form a regular sequence

In a polynomial ring `k[X_σ]` over a field, fix a variable `w` and distinct variables
`s₁, …, sₙ`, all different from `w`. The *graph coordinates*
`X_{sᵢ} - cᵢ X_w^{eᵢ}` form a regular sequence (`graph_isRegular`).

The proof is elementary. Substituting `cⱼ X_w^{eⱼ}` for `X_{sⱼ}` (`j < i`) is a ring map `φ`
with `f - φ f ∈ (g₁, …, g_{i-1})` for every `f`, and `φ` kills these generators. If
`gᵢ f` lies in the ideal, then `gᵢ φ(f) = φ(gᵢ f) = 0`, so `φ f = 0` and `f` lies in the ideal.

This covers both regular sequences of the depth argument: the collision ideal `P_B` in
`ℂ[e₁, …, e_B]` (graph over `e₁`) and the ideal of the diagonal in the source coordinates
(graph over one coefficient of `W`).
-/

noncomputable section

universe u

open MvPolynomial RingTheory.Sequence

namespace KhanSL2.Depth

variable {σ k : Type u} [Field k]

open Classical in
/-- Substitute `q s` for `X s` when `s ∈ T`. -/
def graphSubst (T : Set σ) (q : σ → MvPolynomial σ k) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  aeval fun s => if s ∈ T then q s else X s

open Classical in
theorem graphSubst_X (T : Set σ) (q : σ → MvPolynomial σ k) (s : σ) :
    graphSubst T q (X s) = if s ∈ T then q s else X s := by
  rw [graphSubst, aeval_X]

theorem graphSubst_X_of_mem {T : Set σ} (q : σ → MvPolynomial σ k) {s : σ} (hs : s ∈ T) :
    graphSubst T q (X s) = q s := by
  classical
  rw [graphSubst_X, if_pos hs]

theorem graphSubst_X_of_not_mem {T : Set σ} (q : σ → MvPolynomial σ k) {s : σ} (hs : s ∉ T) :
    graphSubst T q (X s) = X s := by
  classical
  rw [graphSubst_X, if_neg hs]

/-- `f ≡ φ f` modulo the graph coordinates of `T`. -/
theorem sub_graphSubst_mem (T : Set σ) (q : σ → MvPolynomial σ k) (f : MvPolynomial σ k) :
    f - graphSubst T q f ∈ Ideal.span ((fun s => X s - q s) '' T) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [graphSubst, aeval_C, algebraMap_eq, sub_self]
    exact Submodule.zero_mem _
  | add p q' hp hq =>
    rw [map_add, add_sub_add_comm]
    exact Submodule.add_mem _ hp hq
  | mul_X p s hp =>
    rw [map_mul]
    by_cases hs : s ∈ T
    · rw [graphSubst_X_of_mem q hs]
      have h : p * X s - graphSubst T q p * q s =
          (p - graphSubst T q p) * X s + graphSubst T q p * (X s - q s) := by ring
      rw [h]
      exact Submodule.add_mem _ (Ideal.mul_mem_right _ _ hp)
        (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨s, hs, rfl⟩))
    · rw [graphSubst_X_of_not_mem q hs]
      have h : p * X s - graphSubst T q p * X s = (p - graphSubst T q p) * X s := by ring
      rw [h]
      exact Ideal.mul_mem_right _ _ hp

/-- The ideal of the graph coordinates of `T` is the kernel of the substitution, provided the
substitution fixes each `q s`. -/
theorem mem_span_iff_graphSubst_eq_zero {T : Set σ} {q : σ → MvPolynomial σ k}
    (hfix : ∀ s ∈ T, graphSubst T q (q s) = q s) (f : MvPolynomial σ k) :
    f ∈ Ideal.span ((fun s => X s - q s) '' T) ↔ graphSubst T q f = 0 := by
  constructor
  · intro hf
    have hle : Ideal.span ((fun s => X s - q s) '' T) ≤
        RingHom.ker (graphSubst T q : MvPolynomial σ k →+* MvPolynomial σ k) := by
      rw [Ideal.span_le]
      rintro _ ⟨s, hs, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      change graphSubst T q (X s - q s) = 0
      rw [map_sub, graphSubst_X_of_mem q hs, hfix s hs, sub_self]
    exact hle hf
  · intro hf
    have h := sub_graphSubst_mem T q f
    rwa [hf, sub_zero] at h

/-- The monomial target of a graph coordinate. -/
def graphTarget (w : σ) (c : σ → k) (e : σ → ℕ) (s : σ) : MvPolynomial σ k :=
  C (c s) * X w ^ e s

/-- The graph coordinate `X s - c s · X_w ^ e s`. -/
def graphCoord (w : σ) (c : σ → k) (e : σ → ℕ) (s : σ) : MvPolynomial σ k :=
  X s - graphTarget w c e s

theorem graphSubst_graphTarget {T : Set σ} {w : σ} (hw : w ∉ T) (c : σ → k) (e : σ → ℕ)
    (s : σ) : graphSubst T (graphTarget w c e) (graphTarget w c e s) = graphTarget w c e s := by
  rw [graphTarget, map_mul, map_pow, graphSubst_X_of_not_mem _ hw, graphSubst, aeval_C,
    algebraMap_eq]

theorem graphCoord_ne_zero (w : σ) (c : σ → k) (e : σ → ℕ) {s : σ} (hs : s ≠ w) :
    graphCoord w c e s ≠ 0 := by
  classical
  intro h
  set x : σ → k := Function.update (fun _ => 0) s (c s * 0 ^ e s + 1) with hx
  have h1 := congrArg (MvPolynomial.eval x) h
  rw [graphCoord, graphTarget, map_sub, map_mul, map_pow, eval_X, eval_X, eval_C, map_zero] at h1
  have hxs : x s = c s * 0 ^ e s + 1 := by rw [hx, Function.update_self]
  have hxw : x w = 0 := by rw [hx, Function.update_of_ne hs.symm]
  rw [hxs, hxw, add_sub_cancel_left] at h1
  exact one_ne_zero h1

theorem ofList_map_graphCoord (w : σ) (c : σ → k) (e : σ → ℕ) (l : List σ) :
    Ideal.ofList (l.map (graphCoord w c e)) =
      Ideal.span ((fun s => X s - graphTarget w c e s) '' {s | s ∈ l}) := by
  rw [Ideal.ofList]
  congr 1
  ext f
  simp only [Set.mem_setOf_eq, List.mem_map, Set.mem_image]
  rfl

/-- **Graph coordinates form a weakly regular sequence.** -/
theorem graph_isWeaklyRegular (w : σ) (c : σ → k) (e : σ → ℕ) (l : List σ) (hl : l.Nodup)
    (hw : w ∉ l) : IsWeaklyRegular (MvPolynomial σ k) (l.map (graphCoord w c e)) := by
  rw [isWeaklyRegular_iff]
  intro i hi'
  have hi : i < l.length := by simpa using hi'
  rw [List.getElem_map, ← List.map_take, Ideal.smul_eq_mul, Ideal.mul_top,
    isSMulRegular_quotient_iff_mem_of_smul_mem, ofList_map_graphCoord]
  set T : Set σ := {s | s ∈ l.take i}
  have hwT : w ∉ T := fun h => hw (List.mem_of_mem_take h)
  have hfix : ∀ s ∈ T, graphSubst T (graphTarget w c e) (graphTarget w c e s) =
      graphTarget w c e s := fun s _ => graphSubst_graphTarget hwT c e s
  have hsT : l[i] ∉ T := by
    intro h
    rw [Set.mem_setOf_eq, List.mem_take_iff_getElem] at h
    obtain ⟨j, hj, hji⟩ := h
    have := hl.getElem_inj_iff.mp hji
    omega
  intro f hf
  rw [mem_span_iff_graphSubst_eq_zero hfix] at hf ⊢
  rw [smul_eq_mul, map_mul] at hf
  have hg : graphSubst T (graphTarget w c e) (graphCoord w c e l[i]) =
      graphCoord w c e l[i] := by
    rw [graphCoord, map_sub, graphSubst_X_of_not_mem _ hsT, graphSubst_graphTarget hwT]
  rw [hg] at hf
  have hne : graphCoord w c e l[i] ≠ 0 := by
    apply graphCoord_ne_zero
    intro h
    exact hw (h ▸ List.getElem_mem hi)
  exact (mul_eq_zero.mp hf).resolve_left hne

/-- The graph coordinates generate a proper ideal: they all vanish after substituting the
whole graph, which fixes `1`. -/
theorem graph_ofList_ne_top (w : σ) (c : σ → k) (e : σ → ℕ) (l : List σ) (hw : w ∉ l) :
    Ideal.ofList (l.map (graphCoord w c e)) ≠ ⊤ := by
  intro htop
  set T : Set σ := {s | s ∈ l}
  have hwT : w ∉ T := hw
  have hfix : ∀ s ∈ T, graphSubst T (graphTarget w c e) (graphTarget w c e s) =
      graphTarget w c e s := fun s _ => graphSubst_graphTarget hwT c e s
  have h1 : (1 : MvPolynomial σ k) ∈ Ideal.ofList (l.map (graphCoord w c e)) := by
    rw [htop]; exact Submodule.mem_top
  rw [ofList_map_graphCoord, mem_span_iff_graphSubst_eq_zero hfix, map_one] at h1
  exact one_ne_zero h1

/-- **Graph coordinates form a regular sequence.** -/
theorem graph_isRegular (w : σ) (c : σ → k) (e : σ → ℕ) (l : List σ) (hl : l.Nodup)
    (hw : w ∉ l) : IsRegular (MvPolynomial σ k) (l.map (graphCoord w c e)) := by
  refine ⟨graph_isWeaklyRegular w c e l hl hw, fun h => ?_⟩
  apply graph_ofList_ne_top w c e l hw
  rw [Ideal.smul_eq_mul, Ideal.mul_top] at h
  exact h.symm

end KhanSL2.Depth
