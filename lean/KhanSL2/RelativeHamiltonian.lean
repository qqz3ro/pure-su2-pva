module

public import KhanSL2.BCFullDifferential
public import KhanSL2.BCFullBracketEmbedding
public import KhanSL2.BCHamiltonianCalculus
public import KhanSL2.BCColor
public import KhanSL2.CohomologyDescent

@[expose] public section

/-! The Hamiltonian calculation implies differential compatibility on the
relative invariant complex, where the zero-ghost correction vanishes. -/

noncomputable section

namespace KhanSL2

theorem fullDifferential_invariant {u : Cochain} (hu : u ∈ relativeInvariants) :
    fullDifferential (fullInclusion u) = fullInclusion (q u) := by
  rw [fullDifferential_inclusion]
  rw [mem_relativeInvariants_iff] at hu
  simp [hu]

theorem odd_hamiltonian_sign (d : Degree) :
    koszulSign (3, 1, 1) d = koszulSign (1, 0, 0) d := by
  simp [koszulSign, Int.mul_emod]

namespace RelativeHamiltonian

variable
  (hP : IsPVA fullData FullBC.bracket)
  (hΩ : omegaHamiltonian ∈ fullPiece (3, 1, 1))
  (hD : ∀ u, fullDifferential u = FullBC.bracket omegaHamiltonian u 0)

include hP hΩ hD in
theorem differential_bracket (u v : FullCochain) (n : ℕ) :
    fullDifferential (FullBC.bracket u v n) =
      FullBC.bracket (fullDifferential u) v n +
        FullBC.bracket (fullParity u) (fullDifferential v) n := by
  have hh {d : Degree} {a : FullCochain} (ha : a ∈ fullPiece d) :
      fullDifferential (FullBC.bracket a v n) =
        FullBC.bracket (fullDifferential a) v n +
          FullBC.bracket (fullParity a) (fullDifferential v) n := by
    have h := LambdaBracket.zeroMode_bracket hP hΩ ha v n
    simp only [LambdaBracket.zeroMode_apply, ← hD, odd_hamiltonian_sign] at h
    rw [fullParity_of_mem ha]
    simpa only [map_smul, LinearMap.smul_apply, Finsupp.smul_apply] using h
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u w hu hw =>
    simp only [map_add, LinearMap.add_apply, Finsupp.add_apply, hu, hw]
    abel
  | single s r => exact hh (full_single_mem s r)

include hP hΩ hD in
theorem relative_differential_bracket {u v : Cochain}
    (hu : u ∈ relativeInvariants) (hv : v ∈ relativeInvariants) (n : ℕ) :
    q (BC.bracket u v n) =
      BC.bracket (q u) v n + BC.bracket (cochainParity u) (q v) n := by
  apply fullInclusion_injective
  rw [← fullDifferential_invariant (invariant_bracket hu hv n),
    fullInclusion_bracket, differential_bracket hP hΩ hD,
    fullDifferential_invariant hu, fullDifferential_invariant hv,
    ← fullInclusion_parity, map_add, fullInclusion_bracket, fullInclusion_bracket]

include hP hΩ hD in
theorem relative_compatibility : RelativeBracketCompatibility BC.bracket where
  invariant _ _ n hu hv := invariant_bracket hu hv n
  differential _ _ n hu hv := relative_differential_bracket hP hΩ hD hu hv n

end RelativeHamiltonian
end KhanSL2
