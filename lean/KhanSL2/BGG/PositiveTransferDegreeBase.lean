module

public import KhanSL2.BGG.PositiveTransferFiltration
public import KhanSL2.BGG.HarmonicTensorTerms

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.BGG.PositiveTransfer
open PositiveCE FiniteExterior

/-- A pure-tensor membership calculation extends to a base-changed submodule. -/
theorem map_mem_baseChange_of_tmul
    {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module PositiveEnveloping N]
    (P : Submodule ℂ M) (Q : Submodule PositiveEnveloping N)
    (F : PositiveEnveloping ⊗[ℂ] M →ₗ[PositiveEnveloping] N)
    (hF : ∀ a m, m ∈ P → F (a ⊗ₜ[ℂ] m) ∈ Q)
    {u : PositiveEnveloping ⊗[ℂ] M} (hu : u ∈ P.baseChange PositiveEnveloping) : F u ∈ Q := by
  obtain ⟨v, rfl⟩ := Submodule.toBaseChange_surjective' PositiveEnveloping P hu
  clear hu
  induction v using TensorProduct.inductionOn with
  | tmul a m =>
    rw [Submodule.coe_toBaseChange_tmul]
    exact hF a m m.property
  | add v w hv hw =>
    simp only [map_add, Submodule.coe_add]
    exact Q.add_mem hv hw

/-- Exterior degree p in the actual free CE module. -/
def sourceDegree (p : ℕ) : Submodule PositiveEnveloping Chain :=
  (Finsupp.supported ℂ ℂ {s : Finset Mode | s.card = p}).baseChange PositiveEnveloping

/-- The same degree condition in the proved free exterior coordinates. -/
def coordinateDegree (p : ℕ) : Submodule PositiveEnveloping Chain :=
  (Finsupp.supported PositiveEnveloping PositiveEnveloping {s : Finset Mode | s.card=p}).comap
    coefficients.toLinearMap

theorem tmul_mem_coordinateDegree (a : PositiveEnveloping) {u : Cochain} {p : ℕ}
    (hu : u ∈ Finsupp.supported ℂ ℂ {s : Finset Mode | s.card=p}) :
    a ⊗ₜ[ℂ] u ∈ coordinateDegree p := by
  intro s hs
  have hc : coefficients (a ⊗ₜ[ℂ] u) s ≠ 0 := Finsupp.mem_support_iff.mp hs
  have hsu : u s ≠ 0 := by
    intro h
    apply hc
    rw [coefficients_tmul_apply, h, zero_smul]
  exact hu (Finsupp.mem_support_iff.mpr hsu)

/-- The base-changed degree submodule has exactly the intended exterior coefficient support. -/
theorem sourceDegree_eq_coordinateDegree (p : ℕ) : sourceDegree p = coordinateDegree p := by
  apply le_antisymm
  · intro u hu
    exact map_mem_baseChange_of_tmul _ _ LinearMap.id
      (fun a v hv => tmul_mem_coordinateDegree a hv) hu
  · intro u hu
    rw [eq_sum_tmul u]
    apply (sourceDegree p).sum_mem
    intro s hs
    apply Submodule.tmul_mem_baseChange_of_mem
    exact Finsupp.single_mem_supported ℂ 1 (hu hs)

theorem mem_sourceDegree_iff (u : Chain) (p : ℕ) :
    u ∈ sourceDegree p ↔ ∀ s ∈ (coefficients u).support, s.card=p := by
  rw [sourceDegree_eq_coordinateDegree]
  rfl

/-- The actual unperturbed homotopy raises exterior degree by one. -/
theorem base_homotopy_mem_degree {p : ℕ} {u : Chain} (hu : u ∈ sourceDegree p) :
    baseContraction.homotopy u ∈ sourceDegree (p+1) := by
  have hcoeff := (mem_sourceDegree_iff u p).mp hu
  rw [eq_sum_tmul u]
  simp only [map_sum, baseContraction_homotopy_tmul]
  apply (sourceDegree (p+1)).sum_mem
  intro s hs
  apply Submodule.tmul_mem_baseChange_of_mem
  have hm : monomial s ∈ piece s.card (monomialEnergy s) :=
    Finsupp.single_mem_supported ℂ 1 ⟨rfl,rfl⟩
  have hh := PositiveCE.homotopy_mem_piece hm
  intro t ht
  exact (hh ht).1.trans (congrArg (fun k : ℕ => k+1) (hcoeff s hs))

/-- The actual perturbation lowers exterior degree by one. -/
theorem action_mem_degree {p : ℕ} {u : Chain} (hu : u ∈ sourceDegree (p+1)) :
    FreeCE.action u ∈ sourceDegree p := by
  have hcoeff := (mem_sourceDegree_iff u (p+1)).mp hu
  rw [eq_sum_tmul u]
  simp only [map_sum, FreeCE.action_tmul_monomial]
  apply (sourceDegree p).sum_mem
  intro s hs
  apply (sourceDegree p).sum_mem
  intro m hm
  rw [contract, contraction_monomial, if_pos hm]
  apply Submodule.tmul_mem_baseChange_of_mem
  have he : (s.erase m).card=p := by rw [Finset.card_erase_of_mem hm, hcoeff s hs]; omega
  exact (Finsupp.supported ℂ ℂ {t : Finset Mode | t.card=p}).smul_mem _
    (Finsupp.single_mem_supported ℂ 1 he)

/-- The perturbation vanishes in exterior degree zero. -/
theorem action_eq_zero_of_degree_zero {u : Chain} (hu : u ∈ sourceDegree 0) :
    FreeCE.action u = 0 := by
  have hcoeff := (mem_sourceDegree_iff u 0).mp hu
  rw [eq_sum_tmul u, map_sum]
  apply Finset.sum_eq_zero
  intro s hs
  have he : s=∅ := Finset.card_eq_zero.mp (hcoeff s hs)
  subst s
  exact FreeCE.action_tmul_one _

/-- Unperturbed harmonic inclusion preserves exterior degree. -/
theorem base_incl_mem_degree {p : ℕ} {u : HarmonicChain} (hu : u ∈ harmonicTensorDegree p) :
    baseContraction.incl u ∈ sourceDegree p := by
  apply map_mem_baseChange_of_tmul (PositiveCE.harmonicDegree p).toSubmodule
    (sourceDegree p) baseContraction.incl ?_ hu
  intro a v hv
  rw [baseContraction_incl_tmul]
  exact Submodule.tmul_mem_baseChange_of_mem a hv

/-- Unperturbed harmonic projection preserves exterior degree. -/
theorem base_proj_mem_degree {p : ℕ} {u : Chain} (hu : u ∈ sourceDegree p) :
    baseContraction.proj u ∈ harmonicTensorDegree p := by
  have hcoeff := (mem_sourceDegree_iff u p).mp hu
  rw [eq_sum_tmul u]
  simp only [map_sum, baseContraction_proj_tmul]
  apply (harmonicTensorDegree p).sum_mem
  intro s hs
  apply Submodule.tmul_mem_baseChange_of_mem
  have hm : monomial s ∈ piece s.card (monomialEnergy s) :=
    Finsupp.single_mem_supported ℂ 1 ⟨rfl,rfl⟩
  have hh := PositiveCE.harmonicProjection_mem_piece hm
  exact fun t ht => (hh ht).1.trans (hcoeff s hs)

end KhanSL2.BGG.PositiveTransfer
