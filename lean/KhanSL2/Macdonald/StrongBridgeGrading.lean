module

public import KhanSL2.Macdonald.StrongBridgeAlgebra
public import KhanSL2.Macdonald.RestrictedTranspose
public import KhanSL2.StrongMacdonald.Grading

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The coordinate equivalence preserves the finite physical-weight and
symmetric-degree pieces used for restricted duality. -/
noncomputable section
namespace KhanSL2.Macdonald

@[simp] theorem strongExponent_polynomialWeight (e : StrongMacdonald.Exp) :
    polynomialWeight (strongExponentEquiv e) = e.sum (fun g n => n*g.index) := by
  simp only [polynomialWeight, strongExponentEquiv, Finsupp.domCongr_apply,
    Finsupp.sum_equivMapDomain, strongModeEquiv]
  apply Finsupp.sum_congr
  intro g hg
  exact Nat.mul_comm _ _

@[simp] theorem strongExponent_polynomialDegree (e : StrongMacdonald.Exp) :
    polynomialDegree (strongExponentEquiv e) = e.sum (fun _ n => n) := by
  simp [polynomialDegree, strongExponentEquiv, Finsupp.sum_equivMapDomain]

@[simp] theorem strongIndex_weight (e : StrongMacdonald.Exp) (t : Finset Mode) :
    weight (strongExponentEquiv e,t) = StrongMacdonald.wtVal e t := by
  simp [weight, StrongMacdonald.wtVal, StrongMacdonald.diagVal, exteriorWeight]

@[simp] theorem strongIndex_symmetricDegree (e : StrongMacdonald.Exp) (t : Finset Mode) :
    symmetricDegree (strongExponentEquiv e,t) = StrongMacdonald.sdVal e t := by
  simp [symmetricDegree, StrongMacdonald.sdVal, StrongMacdonald.diagVal]

@[simp] theorem basis_repr_strongModel (u : StrongMacdonald.W)
    (e : StrongMacdonald.Exp) (t : Finset Mode) :
    basis.repr (strongModel u) (strongExponentEquiv e,t) = StrongMacdonald.coefW u e t := by
  refine StrongMacdonald.mono_induction (P := fun u =>
    basis.repr (strongModel u) (strongExponentEquiv e,t) = StrongMacdonald.coefW u e t)
    ?_ ?_ ?_ ?_ u
  · simp
  · intro u v hu hv
    simp only [map_add, Finsupp.add_apply, StrongMacdonald.coefW_add, hu, hv]
  · intro c u hu
    simp only [map_smul, Finsupp.smul_apply, StrongMacdonald.coefW_smul, smul_eq_mul, hu]
  · intro f s
    rw [strongModel_mono, Module.Basis.repr_self,
      StrongMacdonald.coefW_mono]
    simp [Finsupp.single_apply, Prod.ext_iff]

theorem strongPiece_support_iff (u : StrongMacdonald.W) (w s : ℕ) :
    u ∈ StrongMacdonald.piece w s ↔ ∀ e t, StrongMacdonald.coefW u e t ≠ 0 →
      StrongMacdonald.wtVal e t = w ∧ StrongMacdonald.sdVal e t = s := by
  constructor
  · intro hu e t hc
    have hw := StrongMacdonald.coefW_diagDer (fun g => g.index) (fun g => g.index+1) u e t
    have hs := StrongMacdonald.coefW_diagDer (fun _ => 1) (fun _ => 0) u e t
    change StrongMacdonald.coefW (StrongMacdonald.Wt u) e t = _ at hw
    change StrongMacdonald.coefW (StrongMacdonald.Sd u) e t = _ at hs
    rw [hu.1, StrongMacdonald.coefW_smul] at hw
    rw [hu.2, StrongMacdonald.coefW_smul] at hs
    constructor
    · exact_mod_cast (mul_right_cancel₀ hc hw).symm
    · exact_mod_cast (mul_right_cancel₀ hc hs).symm
  · intro h
    constructor
    · apply AddMonoidAlgebra.coeff_injective
      ext e t
      change StrongMacdonald.coefW (StrongMacdonald.Wt u) e t =
        StrongMacdonald.coefW ((w : ℂ) • u) e t
      rw [StrongMacdonald.Wt, StrongMacdonald.coefW_diagDer, StrongMacdonald.coefW_smul]
      by_cases hc : StrongMacdonald.coefW u e t = 0
      · simp [hc]
      · change (StrongMacdonald.wtVal e t : ℂ) * StrongMacdonald.coefW u e t = _
        rw [(h e t hc).1]
    · apply AddMonoidAlgebra.coeff_injective
      ext e t
      change StrongMacdonald.coefW (StrongMacdonald.Sd u) e t =
        StrongMacdonald.coefW ((s : ℂ) • u) e t
      rw [StrongMacdonald.Sd, StrongMacdonald.coefW_diagDer, StrongMacdonald.coefW_smul]
      by_cases hc : StrongMacdonald.coefW u e t = 0
      · simp [hc]
      · change (StrongMacdonald.sdVal e t : ℂ) * StrongMacdonald.coefW u e t = _
        rw [(h e t hc).2]

/-- The imported eigenspace and the actual finite monomial piece coincide. -/
theorem strongModel_mem_weightDegreePiece (u : StrongMacdonald.W) (w s : ℕ) :
    strongModel u ∈ weightDegreePiece w s ↔ u ∈ StrongMacdonald.piece w s := by
  rw [mem_weightDegreePiece_iff, strongPiece_support_iff]
  constructor
  · intro h e t hc
    have hb : (strongExponentEquiv e,t) ∈ (basis.repr (strongModel u)).support := by
      rw [Finsupp.mem_support_iff, basis_repr_strongModel]
      exact hc
    simpa only [strongIndex_weight, strongIndex_symmetricDegree] using h _ hb
  · intro h b hb
    obtain ⟨d,t⟩ := b
    obtain ⟨e,rfl⟩ := strongExponentEquiv.surjective d
    have hc : StrongMacdonald.coefW u e t ≠ 0 := by
      simpa only [Finsupp.mem_support_iff, basis_repr_strongModel] using hb
    simpa only [strongIndex_weight, strongIndex_symmetricDegree] using h e t hc

end KhanSL2.Macdonald
