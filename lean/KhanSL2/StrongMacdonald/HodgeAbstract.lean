module

public import KhanSL2.StrongMacdonald.Herm
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-!
# Finite-dimensional Hodge theory for the FGT metric

Let `d` have adjoint `d†` for the positive definite form `herm` on `W`, and let `V ⊆ W` be a
finite-dimensional subspace stable under `d` and `d†`, with `d² = 0` on `V`. Then every
`d`-cocycle in `V` is uniquely the sum of a harmonic element of `V` (killed by `d` and `d†`)
and a coboundary of an element of `V`; a harmonic coboundary vanishes.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace KhanSL2.StrongMacdonald

/-- The abstract Laplacian `d d† + d† d`. -/
def absLap (d dd : Module.End ℂ W) : Module.End ℂ W := d * dd + dd * d

section Abstract

variable {d dd : Module.End ℂ W}

theorem isAdj_absLap (hadj : IsAdj d dd) : IsAdj (absLap d dd) (absLap d dd) := by
  unfold absLap
  exact (hadj.comp hadj.symm).add (hadj.symm.comp hadj)

theorem herm_absLap_self (hadj : IsAdj d dd) (x : W) :
    herm (absLap d dd x) x = herm (dd x) (dd x) + herm (d x) (d x) := by
  rw [absLap, LinearMap.add_apply, herm_add_left, Module.End.mul_apply, Module.End.mul_apply,
    hadj (dd x) x, hadj.symm (d x) x]

theorem absLap_eq_zero_iff (hadj : IsAdj d dd) (x : W) :
    absLap d dd x = 0 ↔ d x = 0 ∧ dd x = 0 := by
  constructor
  · intro h
    have h1 := herm_absLap_self hadj x
    rw [h, herm_zero_left] at h1
    rw [herm_self, herm_self, ← Complex.ofReal_add, eq_comm, Complex.ofReal_eq_zero] at h1
    have h2 := hnormSq_nonneg (dd x)
    have h3 := hnormSq_nonneg (d x)
    exact ⟨hnormSq_eq_zero (by linarith), hnormSq_eq_zero (by linarith)⟩
  · rintro ⟨h1, h2⟩
    rw [absLap, LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, h1, h2,
      map_zero, map_zero, add_zero]

/-- A harmonic coboundary vanishes. -/
theorem eq_zero_of_dd_eq_zero_of_eq_d (hadj : IsAdj d dd) {h u : W} (hh : dd h = 0)
    (hu : h = d u) : h = 0 := by
  apply herm_self_eq_zero
  conv_lhs => arg 1; rw [hu]
  rw [hadj u h, hh, herm_zero_right]

variable {V : Submodule ℂ W} [FiniteDimensional ℂ V]

/-- `V = ker Δ ⊕ im Δ` for the Laplacian restricted to a finite-dimensional stable `V`. -/
theorem exists_absLap_decomp (hadj : IsAdj d dd) (hd : ∀ x ∈ V, d x ∈ V)
    (hdd : ∀ x ∈ V, dd x ∈ V) {x : W} (hx : x ∈ V) :
    ∃ h ∈ V, absLap d dd h = 0 ∧ ∃ y ∈ V, x = h + absLap d dd y := by
  have hL : ∀ x ∈ V, absLap d dd x ∈ V := fun x hx =>
    V.add_mem (hd _ (hdd x hx)) (hdd _ (hd x hx))
  set Lr : V →ₗ[ℂ] V := (absLap d dd).restrict hL with hLr
  have hdisj : LinearMap.ker Lr ⊓ LinearMap.range Lr = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hv1, ⟨u, rfl⟩⟩
    rw [Submodule.mem_bot]
    have hv : absLap d dd (absLap d dd u) = 0 := by
      have := congrArg Subtype.val (LinearMap.mem_ker.mp hv1)
      simpa [hLr] using this
    apply Subtype.ext
    apply herm_self_eq_zero
    change herm (absLap d dd u) (absLap d dd u) = 0
    rw [isAdj_absLap hadj u, hv, herm_zero_right]
  have htop : LinearMap.ker Lr ⊔ LinearMap.range Lr = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker Lr) (LinearMap.range Lr)
    have h2 := LinearMap.finrank_range_add_finrank_ker Lr
    rw [hdisj, finrank_bot] at h1
    omega
  have hmem : (⟨x, hx⟩ : V) ∈ LinearMap.ker Lr ⊔ LinearMap.range Lr := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨h, hh, z, ⟨y, rfl⟩, hsum⟩ := Submodule.mem_sup.mp hmem
  refine ⟨h, h.2, ?_, y, y.2, ?_⟩
  · have := congrArg Subtype.val (LinearMap.mem_ker.mp hh)
    simpa [hLr] using this
  · have := congrArg Subtype.val hsum
    simpa [hLr] using this.symm

/-- Hodge decomposition of cocycles: every `d`-cocycle of `V` is a harmonic element of `V`
plus a coboundary of an element of `V`. -/
theorem exists_harmonic_add_d (hadj : IsAdj d dd) (hd : ∀ x ∈ V, d x ∈ V)
    (hdd : ∀ x ∈ V, dd x ∈ V) (hd2 : ∀ x ∈ V, d (d x) = 0) {z : W} (hz : z ∈ V)
    (hdz : d z = 0) :
    ∃ h ∈ V, d h = 0 ∧ dd h = 0 ∧ ∃ u ∈ V, z = h + d u := by
  obtain ⟨h, hV, hh, y, hy, rfl⟩ := exists_absLap_decomp hadj hd hdd hz
  obtain ⟨hh1, hh2⟩ := (absLap_eq_zero_iff hadj h).mp hh
  refine ⟨h, hV, hh1, hh2, dd y, hdd y hy, ?_⟩
  -- the component `d† d y` vanishes
  have hw : d (dd (d y)) = 0 := by
    have h1 : d (h + absLap d dd y) = d h + d (d (dd y)) + d (dd (d y)) := by
      rw [absLap, LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, map_add,
        map_add, add_assoc]
    rw [hdz, hh1, hd2 _ (hdd y hy), zero_add, zero_add] at h1
    exact h1.symm
  have hw0 : dd (d y) = 0 := by
    apply herm_self_eq_zero
    rw [hadj.symm (d y) (dd (d y)), hw, herm_zero_right]
  rw [absLap, LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, hw0, add_zero]

/-- The harmonic representative is unique. -/
theorem harmonic_unique (hadj : IsAdj d dd) {h h' u u' : W} (hh : dd h = 0) (hh' : dd h' = 0)
    (heq : h + d u = h' + d u') : h = h' := by
  have h1 : h - h' = d (u' - u) := by
    rw [map_sub, sub_eq_sub_iff_add_eq_add, add_comm (d u')]
    exact heq
  have h2 : dd (h - h') = 0 := by rw [map_sub, hh, hh', sub_zero]
  exact sub_eq_zero.mp (eq_zero_of_dd_eq_zero_of_eq_d hadj h2 h1)

end Abstract

end KhanSL2.StrongMacdonald
