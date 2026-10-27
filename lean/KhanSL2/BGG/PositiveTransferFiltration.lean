module

public import KhanSL2.BGG.PositiveTransferBase
public import KhanSL2.BGG.FiltrationNilpotence
public import TauCeti.Algebra.Homology.Contraction.Perturbation

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Exterior-energy lowering proves that the actual perturbation series is
pointwise finite, over the noncommutative positive-current enveloping algebra. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.BGG.PositiveTransfer

open PositiveCE FiniteExterior

/-- Strict exterior-energy filtration. Coefficient energy is unrestricted. -/
def filtration (n : ℕ) : Submodule PositiveEnveloping Chain :=
  (Finsupp.supported PositiveEnveloping PositiveEnveloping
    {s : Finset Mode | monomialEnergy s < n}).comap coefficients.toLinearMap

theorem mem_filtration_iff (u : Chain) (n : ℕ) :
    u ∈ filtration n ↔ ∀ s ∈ (coefficients u).support, monomialEnergy s < n := Iff.rfl

theorem filtration_mono : Monotone filtration := by
  intro n m hnm u hu s hs
  exact lt_of_lt_of_le (hu hs) hnm

@[simp] theorem filtration_zero : filtration 0 = ⊥ := by
  apply le_antisymm
  · intro u hu
    change u = 0
    apply coefficients.injective
    apply Finsupp.ext
    intro s
    by_cases hs : coefficients u s = 0
    · simpa using hs
    · have h : monomialEnergy s < 0 := hu (Finsupp.mem_support_iff.mpr hs)
      omega
  · exact bot_le

/-- Every actual free chain has a finite exterior-energy bound. -/
theorem filtration_exhaustive (u : Chain) : ∃ n, u ∈ filtration n := by
  classical
  refine ⟨(coefficients u).support.sup monomialEnergy + 1, ?_⟩
  intro s hs
  change monomialEnergy s < (coefficients u).support.sup monomialEnergy + 1
  have h : monomialEnergy s ≤ (coefficients u).support.sup monomialEnergy :=
    Finset.le_sup (f := monomialEnergy) hs
  exact Nat.lt_succ_of_le h

/-- A support bound on the exterior factor bounds every tensor, regardless of coefficient. -/
theorem tmul_mem_filtration (a : PositiveEnveloping) {u : Cochain} {n : ℕ}
    (hu : u ∈ Finsupp.supported ℂ ℂ {s : Finset Mode | monomialEnergy s < n}) :
    a ⊗ₜ[ℂ] u ∈ filtration n := by
  intro s hs
  have hc : coefficients (a ⊗ₜ[ℂ] u) s ≠ 0 := Finsupp.mem_support_iff.mp hs
  have hsu : u s ≠ 0 := by
    intro h
    apply hc
    rw [coefficients_tmul_apply, h, zero_smul]
  exact hu (Finsupp.mem_support_iff.mpr hsu)

theorem tmul_monomial_mem_filtration (a : PositiveEnveloping) (s : Finset Mode) {n : ℕ}
    (hs : monomialEnergy s < n) : a ⊗ₜ[ℂ] monomial s ∈ filtration n :=
  tmul_mem_filtration a (Finsupp.single_mem_supported ℂ 1 hs)

/-- The base-changed actual harmonic homotopy preserves exterior energy. -/
theorem homotopy_mem_filtration {n : ℕ} {u : Chain} (hu : u ∈ filtration n) :
    baseContraction.homotopy u ∈ filtration n := by
  rw [eq_sum_tmul u]
  simp only [map_sum, baseContraction_homotopy_tmul]
  apply (filtration n).sum_mem
  intro s hs
  apply tmul_mem_filtration
  have hm : monomial s ∈ piece s.card (monomialEnergy s) :=
    Finsupp.single_mem_supported ℂ 1 ⟨rfl, rfl⟩
  have hh := PositiveCE.homotopy_mem_piece hm
  intro t ht
  change monomialEnergy t < n
  rw [(hh ht).2]
  exact hu hs

/-- Erasing an occupied positive mode strictly lowers physical exterior energy. -/
theorem monomialEnergy_erase_lt {s : Finset Mode} {m : Mode} (hm : m ∈ s) :
    monomialEnergy (s.erase m) < monomialEnergy s := by
  have hsum := Finset.sum_erase_add (s := s) (fun a : Mode => a.index+1) hm
  change monomialEnergy (s.erase m) + (m.index+1) = monomialEnergy s at hsum
  omega

/-- The actual action part strictly lowers exterior energy. -/
theorem action_mem_filtration {n : ℕ} {u : Chain} (hu : u ∈ filtration (n+1)) :
    FreeCE.action u ∈ filtration n := by
  rw [eq_sum_tmul u]
  simp only [map_sum, FreeCE.action_tmul_monomial]
  apply (filtration n).sum_mem
  intro s hs
  apply (filtration n).sum_mem
  intro m hm
  have he : monomialEnergy (s.erase m) < n := by
    have hsm := monomialEnergy_erase_lt hm
    have hsn : monomialEnergy s < n+1 := hu hs
    omega
  rw [contract, contraction_monomial, if_pos hm]
  apply tmul_mem_filtration
  exact (Finsupp.supported ℂ ℂ {t : Finset Mode | monomialEnergy t < n}).smul_mem _
    (Finsupp.single_mem_supported ℂ 1 he)

/-- An explicit finite bound for each actual action-homotopy composite. -/
theorem action_homotopy_pow_eq_zero {n : ℕ} {u : Chain} (hu : u ∈ filtration n) :
    ((FreeCE.action * baseContraction.homotopy)^n) u = 0 := by
  apply pow_eq_zero_of_filtration filtration filtration_zero
    (FreeCE.action * baseContraction.homotopy) ?_ n hu
  intro k v hv
  change FreeCE.action (baseContraction.homotopy v) ∈ filtration k
  exact action_mem_filtration (homotopy_mem_filtration hv)

/-- The actual perturbation is pointwise nilpotent; there is no completed tensor product. -/
theorem action_homotopy_locallyNilpotent (u : Chain) :
    ∃ n : ℕ, ((FreeCE.action * baseContraction.homotopy)^n) u = 0 := by
  obtain ⟨n, hn⟩ := filtration_exhaustive u
  exact ⟨n, action_homotopy_pow_eq_zero hn⟩

/-- The inverse needed for the actual finite homological perturbation lemma exists. -/
theorem isUnit_one_add_action_homotopy : IsUnit (1 + FreeCE.action * baseContraction.homotopy) :=
  Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero _ action_homotopy_locallyNilpotent

end KhanSL2.BGG.PositiveTransfer
