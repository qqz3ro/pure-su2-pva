module

public import KhanSL2.BGG.PositiveContractionGrading

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Physical-energy dilation on the actual positive exterior complex and its harmonics. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.BGG.PositiveCE

/-- Dilation by two on each actual exterior monomial. -/
def energyScale : Module.End ℂ Cochain :=
  Finsupp.linearCombination ℂ (fun s => (2 : ℂ) ^ monomialEnergy s • FiniteExterior.monomial s)

@[simp] theorem energyScale_monomial (s : Finset Mode) :
    energyScale (FiniteExterior.monomial s) = (2 : ℂ) ^ monomialEnergy s • FiniteExterior.monomial s := by
  simp [energyScale, FiniteExterior.monomial]

/-- Dilation has the prescribed scalar value on each genuine energy eigenspace. -/
theorem energyScale_of_energy (N : ℕ) (u : Cochain) (hu : energyOp u = (N : ℂ) • u) :
    energyScale u = (2 : ℂ) ^ N • u := by
  have hs : ∀ s ∈ u.support, monomialEnergy s = N :=
    (FiniteExterior.euler_nat_eq_smul_iff (fun m : Mode => m.index + 1) N u).mp hu
  rw [FiniteExterior.eq_sum_support u]
  simp only [map_sum, map_smul, energyScale_monomial, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s hsu
  rw [hs s hsu]
  exact smul_comm _ _ _

theorem energyScale_of_piece {p N : ℕ} {u : Cochain} (hu : u ∈ piece p N) :
    energyScale u = (2 : ℂ) ^ N • u := energyScale_of_energy N u ((mem_piece_iff_euler u p N).mp hu).2

/-- An operator commuting with the actual energy Euler operator commutes with dilation. -/
theorem energyScale_commute_of_energy (f : Module.End ℂ Cochain)
    (hf : ∀ u, energyOp (f u) = f (energyOp u)) (u : Cochain) :
    energyScale (f u) = f (energyScale u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | single s r =>
    have hr : Finsupp.single s r = r • FiniteExterior.monomial s := by simp [FiniteExterior.monomial]
    rw [hr, map_smul, map_smul, map_smul, map_smul]
    congr 1
    rw [energyScale_monomial, map_smul]
    apply energyScale_of_energy
    rw [hf, energyOp_monomial, map_smul]

/-- The same compatibility follows from preservation of actual bidegree pieces. -/
theorem energyScale_commute_of_piece (f : Module.End ℂ Cochain) (q : ℕ → ℕ)
    (hf : ∀ p N, ∀ u ∈ piece p N, f u ∈ piece (q p) N) (u : Cochain) :
    energyScale (f u) = f (energyScale u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | single s r =>
    have hr : Finsupp.single s r = r • FiniteExterior.monomial s := by simp [FiniteExterior.monomial]
    rw [hr, map_smul, map_smul, map_smul, map_smul]
    congr 1
    rw [energyScale_monomial, map_smul]
    apply energyScale_of_piece
    exact hf s.card (monomialEnergy s) _ (Finsupp.single_mem_supported ℂ 1 ⟨rfl,rfl⟩)

@[simp] theorem energyScale_boundary (u : Cochain) :
    energyScale (boundary u) = boundary (energyScale u) :=
  energyScale_commute_of_energy boundary energyOp_boundary u

@[simp] theorem energyScale_d (u : Cochain) : energyScale (d u) = d (energyScale u) :=
  energyScale_commute_of_energy d energyOp_d u

@[simp] theorem energyScale_laplacian (u : Cochain) :
    energyScale (laplacian u) = laplacian (energyScale u) := by
  simp only [laplacian_apply, map_add, energyScale_boundary, energyScale_d]

@[simp] theorem energyScale_homotopy (u : Cochain) :
    energyScale (chainContraction.homotopy u) = chainContraction.homotopy (energyScale u) :=
  energyScale_commute_of_piece chainContraction.homotopy (fun p => p + 1)
    (fun _ _ _ hu => homotopy_mem_piece hu) u

/-- Dilation restricts to the actual kernel of the Laplacian. -/
def harmonicEnergyScale : Module.End ℂ Harmonic where
  toFun u := ⟨energyScale u, by
    change laplacian (energyScale u) = 0
    rw [← energyScale_laplacian, show laplacian u = 0 from u.property, map_zero]⟩
  map_add' u v := Subtype.ext (energyScale.map_add u v)
  map_smul' r u := Subtype.ext (energyScale.map_smul r u)

@[simp] theorem harmonicEnergyScale_coe (u : Harmonic) :
    (harmonicEnergyScale u : Cochain) = energyScale u := rfl

@[simp] theorem harmonicEnergyScale_projection (u : Cochain) :
    harmonicEnergyScale (harmonicProjection u) = harmonicProjection (energyScale u) := by
  apply Subtype.ext
  exact energyScale_commute_of_piece (Harmonic.subtype.comp harmonicProjection) id
    (fun _ _ _ hu => harmonicProjection_mem_piece hu) u

/-- Contraction removes exactly the physical energy of its mode. -/
theorem energyScale_contract (m : Mode) (u : Cochain) :
    (2 : ℂ) ^ (m.index + 1) • energyScale (contract m u) = contract m (energyScale u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, smul_add, hu, hv]
  | single s r =>
    have hr : Finsupp.single s r = r • FiniteExterior.monomial s := by simp [FiniteExterior.monomial]
    rw [hr, map_smul, map_smul, map_smul, map_smul]
    rw [smul_comm ((2 : ℂ) ^ (m.index + 1)) r]
    congr 1
    by_cases hm : m ∈ s
    · have hE : monomialEnergy (s.erase m) + (m.index + 1) = monomialEnergy s :=
        Finset.sum_erase_add _ _ hm
      simp only [contract, FiniteExterior.contraction_monomial, if_pos hm,
        map_smul, energyScale_monomial, smul_smul]
      rw [← hE, pow_add]
      congr 1
      ring
    · simp only [contract, FiniteExterior.contraction_monomial, if_neg hm,
        map_zero, smul_zero, energyScale_monomial, map_smul]

end KhanSL2.BGG.PositiveCE
