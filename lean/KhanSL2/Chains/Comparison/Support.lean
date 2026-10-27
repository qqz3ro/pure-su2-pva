module

public import KhanSL2.Chains.Comparison.Setup

@[expose] public section

/-!
# Support conditions

`q u` only involves monomials containing a `c`-generator, while the image of the
coefficient factor `Λ(ε𝔩)` only involves monomials of `b`-generators. Hence they
pair to zero.
-/

noncomputable section

namespace KhanSL2.Current

open FiniteExterior

/-- Cochains all of whose monomials contain a `c`-generator. -/
def HasC : Submodule ℂ Cochain := Finsupp.supported ℂ ℂ {s | ∃ m ∈ s, m.bCount = 0}

/-- Cochains all of whose monomials consist of `b`-generators. -/
def PureB : Submodule ℂ Cochain := Finsupp.supported ℂ ℂ {s | ∀ m ∈ s, m.bCount = 1}

theorem monomialWedge_mem_supported {P : ExteriorMonomial → Prop} {s t : ExteriorMonomial}
    (h : Disjoint s t → P (s ∪ t)) :
    monomialWedge s t ∈ Finsupp.supported ℂ ℂ {x | P x} := by
  unfold monomialWedge
  split_ifs with hd
  · exact Finsupp.single_mem_supported ℂ _ (h hd)
  · exact Submodule.zero_mem _

theorem wedge_mem_supported {P : ExteriorMonomial → Prop} {u v : Cochain}
    (hP : ∀ s t, s ∈ u.support → t ∈ v.support → Disjoint s t → P (s ∪ t)) :
    wedge u v ∈ Finsupp.supported ℂ ℂ {x | P x} := by
  rw [wedge, wedgeLinear, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro s hs
  rw [LinearMap.smul_apply, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro t ht
  apply Submodule.smul_mem
  exact monomialWedge_mem_supported (hP s t hs ht)

theorem wedge_mem_HasC_left {u v : Cochain} (hu : u ∈ HasC) : wedge u v ∈ HasC := by
  apply wedge_mem_supported
  intro s t hs _ _
  obtain ⟨m, hm, hb⟩ := hu hs
  exact ⟨m, Finset.mem_union_left _ hm, hb⟩

theorem mul_mem_PureB {u v : Cochain} (hu : u ∈ PureB) (hv : v ∈ PureB) : u * v ∈ PureB := by
  apply wedge_mem_supported
  intro s t hs ht _ m hm
  rcases Finset.mem_union.mp hm with hm | hm
  · exact hu hs m hm
  · exact hv ht m hm

theorem generator_c_mem_HasC (i : ℕ) (b : Fin 3) : generator (Mode.c i b) ∈ HasC :=
  Finsupp.single_mem_supported ℂ 1 ⟨Mode.c i b, Finset.mem_singleton_self _, rfl⟩

theorem generator_b_mem_PureB (i : ℕ) (b : Fin 3) : generator (Mode.b i b) ∈ PureB :=
  Finsupp.single_mem_supported ℂ 1 (by simp [Mode.bCount])

theorem qGenerator_mem_HasC (m : Mode) : qGenerator m ∈ HasC := by
  cases m with
  | c j a =>
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _
      fun b _ => Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_)
    exact wedge_mem_HasC_left (generator_c_mem_HasC i b)
  | b j a =>
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _
      fun b _ => Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_)
    exact wedge_mem_HasC_left (generator_c_mem_HasC i b)

theorem q_mem_HasC (u : Cochain) : q u ∈ HasC := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | single s r =>
    rw [q, extendDerivation, Finsupp.linearCombination_single]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_)
    exact wedge_mem_HasC_left (qGenerator_mem_HasC m)

theorem phiB_mem_PureB (x : Cur) : phiB x ∈ PureB := by
  rw [phiB, Module.Basis.constr_apply]
  exact Submodule.finsuppSum_mem _ _ _ _ fun p _ =>
    Submodule.smul_mem _ _ (generator_b_mem_PureB _ _)

theorem PhiB_mem_PureB (ν : NB) : PhiB ν ∈ PureB := by
  induction ν using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [AlgHom.commutes]
    exact Finsupp.single_mem_supported ℂ r (by simp)
  | add ν ν' hν hν' => rw [map_add]; exact Submodule.add_mem _ hν hν'
  | ι_mul ν x hν =>
    rw [map_mul, PhiB_ι]
    exact mul_mem_PureB (phiB_mem_PureB x) hν

theorem pairing_HasC_PureB {u v : Cochain} (hu : u ∈ HasC) (hv : v ∈ PureB) :
    pairing u v = 0 := by
  rw [pairing, coefficientPairing, Finsupp.linearCombination_apply, Finsupp.sum,
    LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro s hs
  rw [LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul]
  by_cases hvs : v s = 0
  · rw [hvs, mul_zero]
  · exfalso
    obtain ⟨m, hm, hb⟩ := hu hs
    have := hv (Finsupp.mem_support_iff.mpr hvs) m hm
    rw [hb] at this
    exact zero_ne_one this

theorem pairing_q_PhiB (u : Cochain) (ν : NB) : pairing (q u) (PhiB ν) = 0 :=
  pairing_HasC_PureB (q_mem_HasC u) (PhiB_mem_PureB ν)

end KhanSL2.Current
