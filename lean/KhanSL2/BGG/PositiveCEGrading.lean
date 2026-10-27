module

public import KhanSL2.BGG.ColorRootGrading
public import KhanSL2.BGG.PositiveBoundaryAdjoint

@[expose] public section

/-! Degree and physical-energy preservation for the actual CE operators. -/
noncomputable section
open scoped BigOperators
open KhanSL2.FiniteExterior
namespace KhanSL2.BGG.PositiveCE

private theorem euler_pairing (w : Mode → ℂ) (u v : Cochain) :
    coefficientPairing (euler w u) v = coefficientPairing u (euler w v) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]
  | single s r =>
    have hr : Finsupp.single s r = r • monomial s := by simp [monomial]
    rw [hr, map_smul, euler_monomial]
    simp only [map_smul, LinearMap.smul_apply, coefficientPairing_monomial,
      euler_apply, smul_eq_mul]

private theorem euler_d_of_generator (w : Mode → ℂ) (t : ℂ)
    (hgen : ∀ m : Mode, euler w (d (FiniteExterior.generator m)) =
      (w m+t) • d (FiniteExterior.generator m)) (u : Cochain) :
    euler w (d u) = d (euler w u) + t • d u := by
  induction u using FiniteExterior.induction_on Mode.code with
  | hzero => simp
  | hone =>
    change euler w (d 1) = d (euler w 1) + t • d 1
    rw [d_one, euler_one, map_zero, map_zero, smul_zero, add_zero]
  | hadd u v hu hv => simp only [map_add, hu, hv, smul_add]; abel
  | hsmul r u hu => simp only [map_smul, hu, smul_add, smul_smul]; congr 1; ring
  | hgen m u hu =>
    change euler w (d (FiniteExterior.generator m * u)) =
      d (euler w (FiniteExterior.generator m * u)) + t • d (FiniteExterior.generator m * u)
    simp only [d_mul, euler_mul, euler_generator, map_add, map_smul, parity_generator,
      map_neg, neg_mul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hgen, hu,
      smul_add, smul_smul]
    module

private theorem euler_d_generator_of_split (w : Mode → ℂ) (t : ℂ) (m : Mode)
    (h : ∀ r ∈ Finset.range m.index, ∀ a b : Fin 3,
      w ⟨r,a⟩ + w ⟨m.index-1-r,b⟩ = w m+t) :
    euler w (d (FiniteExterior.generator m)) = (w m+t) • d (FiniteExterior.generator m) := by
  rw [d_generator]
  simp only [map_smul, map_sum]
  have he (r : ℕ) (hr : r ∈ Finset.range m.index) (a b : Fin 3) :
      euler w (FiniteExterior.generator (⟨r,a⟩ : Mode) *
        FiniteExterior.generator (⟨m.index-1-r,b⟩ : Mode)) =
      (w m+t) • (FiniteExterior.generator (⟨r,a⟩ : Mode) *
        FiniteExterior.generator (⟨m.index-1-r,b⟩ : Mode)) := by
    rw [euler_mul, euler_generator, euler_generator,
      smul_mul_assoc, mul_smul_comm, ← add_smul, h r hr a b]
  have hs : (∑ r ∈ Finset.range m.index, ∑ a : Fin 3, ∑ b : Fin 3,
      epsilon m.color a b • euler w (FiniteExterior.generator (⟨r,a⟩ : Mode) *
        FiniteExterior.generator (⟨m.index-1-r,b⟩ : Mode))) =
      (w m+t) • ∑ r ∈ Finset.range m.index, ∑ a : Fin 3, ∑ b : Fin 3,
        epsilon m.color a b • (FiniteExterior.generator (⟨r,a⟩ : Mode) *
          FiniteExterior.generator (⟨m.index-1-r,b⟩ : Mode)) := by
    simp only [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [he r hr, smul_smul, mul_comm (epsilon m.color _ _) (w m+t)]
  rw [hs]
  simp only [smul_smul, mul_comm (-(1/2:ℂ)) (w m+t)]

/-- The CE coboundary preserves physical energy. -/
theorem energyOp_d (u : Cochain) : energyOp (d u) = d (energyOp u) := by
  have h := euler_d_of_generator (fun m : Mode => ((m.index+1:ℕ):ℂ)) 0 (fun m =>
    euler_d_generator_of_split _ 0 m (by
      intro r hr a b
      have hr' := Finset.mem_range.mp hr
      simp only [add_zero]
      norm_cast
      omega)) u
  simpa only [zero_smul, add_zero, energyOp] using h

/-- The CE coboundary raises exterior degree by one. -/
theorem degreeOp_d (u : Cochain) : degreeOp (d u) = d (degreeOp u) + d u := by
  have h := euler_d_of_generator (fun _ : Mode => (1:ℂ)) 1 (fun m =>
    euler_d_generator_of_split _ 1 m (by intros; rfl)) u
  simpa only [one_smul, degreeOp] using h

private theorem euler_boundary_of_d (w : Mode → ℂ) (t : ℂ)
    (hd : ∀ u : Cochain, euler w (d u) = d (euler w u) + t • d u) (u : Cochain) :
    euler w (boundary u) = boundary (euler w u) - t • boundary u := by
  have hp (v : Cochain) : coefficientPairing (euler w (boundary u)) v =
      coefficientPairing (boundary (euler w u) - t • boundary u) v := by
    rw [euler_pairing, boundary_pairing]
    have h : d (euler w v) = euler w (d v) - t • d v := by rw [hd]; abel
    rw [h]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      ← euler_pairing, boundary_pairing]
  apply Finsupp.ext
  intro s
  simpa only [coefficientPairing_monomial_right] using hp (monomial s)

theorem energyOp_boundary (u : Cochain) :
    energyOp (boundary u) = boundary (energyOp u) := by
  have h := euler_boundary_of_d (fun m : Mode => ((m.index+1:ℕ):ℂ)) 0
    (fun v => by simpa only [zero_smul, add_zero, energyOp] using energyOp_d v) u
  simpa only [zero_smul, sub_zero, energyOp] using h

theorem degreeOp_boundary (u : Cochain) :
    degreeOp (boundary u) = boundary (degreeOp u) - boundary u := by
  have h := euler_boundary_of_d (fun _ : Mode => (1:ℂ)) 1
    (fun v => by simpa only [one_smul, degreeOp] using degreeOp_d v) u
  simpa only [one_smul, degreeOp] using h

/-- The actual coboundary maps the specified finite pieces to the next exterior degree. -/
theorem d_mem_piece {p N : ℕ} {u : Cochain} (hu : u ∈ piece p N) :
    d u ∈ piece (p+1) N := by
  obtain ⟨hp,hN⟩ := (mem_piece_iff_euler u p N).mp hu
  apply (mem_piece_iff_euler _ _ _).mpr
  constructor
  · rw [degreeOp_d, hp, map_smul]
    simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  · rw [energyOp_d, hN, map_smul]

/-- The actual boundary lowers exterior degree by one and preserves energy. -/
theorem boundary_mem_piece {p N : ℕ} {u : Cochain} (hu : u ∈ piece (p+1) N) :
    boundary u ∈ piece p N := by
  obtain ⟨hp,hN⟩ := (mem_piece_iff_euler u (p+1) N).mp hu
  apply (mem_piece_iff_euler _ _ _).mpr
  constructor
  · rw [degreeOp_boundary, hp, map_smul]
    simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul, add_sub_cancel_right]
  · rw [energyOp_boundary, hN, map_smul]

end KhanSL2.BGG.PositiveCE