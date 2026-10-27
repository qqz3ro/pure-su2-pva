module

public import KhanSL2.Chains.Comparison.Setup

@[expose] public section

/-!
# Transferring derivations across `Phi`

Let `E` be an even derivation of cochains that sends generators to exterior degree one.
If its transpose agrees, up to sign, with endomorphisms `Dc` of `𝔩₊` and `Db` of `𝔩`
on generators, then it agrees with the Lie derivative `lieDeriv Dc (derivExt Db)` on
all chains:

`⟨E u, Φ ξ⟩ = - ⟨u, Φ (lieDeriv Dc (derivExt Db) ξ)⟩`.

The proof is an induction over chains. Its key input is that the commutator of `E`
with a contraction is again a contraction.
-/

noncomputable section

open scoped TensorProduct

namespace KhanSL2.Current

open LieChains FiniteExterior

/-! ## Coefficients at the empty monomial -/

theorem mul_apply_empty (u v : Cochain) : (u * v) ∅ = u ∅ * v ∅ := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u w hu hw => simp [add_mul, hu, hw]
  | single s r =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp [mul_add, hv, hw]
    | single t c =>
      change (FiniteExterior.wedge _ _ _) ∅ = _
      rw [FiniteExterior.wedge_single, Finsupp.smul_apply, FiniteExterior.monomialWedge]
      by_cases hs : s = ∅
      · subst hs
        by_cases ht : t = ∅
        · subst ht; simp [FiniteExterior.inversionCount]
        · simp [Finsupp.single_apply, Ne.symm ht]
      · have hst : ¬(s ∪ t = ∅) := fun h => hs (Finset.union_eq_empty.mp h).1
        split_ifs <;> simp [Finsupp.single_apply, Ne.symm hs, hst]

theorem apply_empty_of_mem_degOne {v : Cochain} (hv : v ∈ degOne) : v ∅ = 0 := by
  by_contra h
  have := hv (Finsupp.mem_support_iff.mpr h)
  simp at this

theorem generator_apply_empty (m : Mode) : generator m ∅ = 0 :=
  apply_empty_of_mem_degOne (generator_mem_degOne m)

theorem pairing_one_right (u : Cochain) : pairing u 1 = u ∅ := pairing_single_right u ∅

/-! ## Even derivations -/

/-- An even derivation of cochains sending generators to exterior degree one. -/
structure IsEvenGenDer (E : Module.End ℂ Cochain) : Prop where
  map_one : E 1 = 0
  map_gen_mul : ∀ (m : Mode) (u : Cochain),
    E (generator m * u) = E (generator m) * u + generator m * E u
  gen_mem : ∀ m, E (generator m) ∈ degOne

theorem IsEvenGenDer.apply_empty {E : Module.End ℂ Cochain} (hE : IsEvenGenDer E)
    (u : Cochain) : E u ∅ = 0 := by
  induction u using cochain_induction with
  | hzero => simp
  | hone => rw [← cochain_one_eq, hE.map_one]; rfl
  | hadd u v hu hv => simp [hu, hv]
  | hsmul r u hu => simp [hu]
  | hgen m u hu =>
    change E (generator m * u) ∅ = 0
    rw [hE.map_gen_mul, Finsupp.add_apply, mul_apply_empty, mul_apply_empty,
      apply_empty_of_mem_degOne (hE.gen_mem m), hu]
    simp

/-! ## Contractions by elements of `𝔩₊` and `𝔩` -/

theorem ctr_one (m : Mode) : ctr m 1 = 0 := by
  change contraction _ m (monomial ∅) = 0
  simp

theorem ctr_generator_mul (m n : Mode) (u : Cochain) :
    ctr m (generator n * u) = pairing (generator n) (generator m) • u - generator n * ctr m u := by
  have h := contraction_generator_wedge GeneratorOrder.code GeneratorOrder.code_injective m n u
  have e1 : (generator n * u : Cochain) =
      FiniteExterior.wedge GeneratorOrder.code (FiniteExterior.generator n) u := rfl
  have e2 : (generator n * ctr m u : Cochain) =
      FiniteExterior.wedge GeneratorOrder.code (FiniteExterior.generator n) (ctr m u) := rfl
  rw [e1, e2, h]
  congr 1
  rw [show generator n = Finsupp.single {n} (1 : ℂ) from rfl, pairing_single_left]
  by_cases hmn : m = n
  · subst hmn; simp [generator]
  · simp [generator, Finsupp.single_apply, hmn, Ne.symm hmn]

theorem iotaC_one (x : plus) : iotaC x 1 = 0 := by
  have h : (LinearMap.applyₗ (1 : Cochain)) ∘ₗ iotaC = 0 := by
    apply plusBasis.ext; rintro ⟨j, a⟩; simp [ctr_one]
  exact congrArg (fun F => F x) h

theorem iotaB_one (x : Cur) : iotaB x 1 = 0 := by
  have h : (LinearMap.applyₗ (1 : Cochain)) ∘ₗ iotaB = 0 := by
    apply curBasis.ext; rintro ⟨j, a⟩; simp [ctr_one]
  exact congrArg (fun F => F x) h

theorem iotaC_generator_mul (x : plus) (n : Mode) (u : Cochain) :
    iotaC x (generator n * u) = pairing (generator n) (phiC x) • u - generator n * iotaC x u := by
  have h : (LinearMap.applyₗ (generator n * u)) ∘ₗ iotaC =
      (LinearMap.smulRight (pairing (generator n) ∘ₗ phiC) u) -
        (LinearMap.mulLeft ℂ (generator n)) ∘ₗ (LinearMap.applyₗ u) ∘ₗ iotaC := by
    apply plusBasis.ext; rintro ⟨j, a⟩; simp [ctr_generator_mul]
  exact congrArg (fun F => F x) h

theorem iotaB_generator_mul (x : Cur) (n : Mode) (u : Cochain) :
    iotaB x (generator n * u) = pairing (generator n) (phiB x) • u - generator n * iotaB x u := by
  have h : (LinearMap.applyₗ (generator n * u)) ∘ₗ iotaB =
      (LinearMap.smulRight (pairing (generator n) ∘ₗ phiB) u) -
        (LinearMap.mulLeft ℂ (generator n)) ∘ₗ (LinearMap.applyₗ u) ∘ₗ iotaB := by
    apply curBasis.ext; rintro ⟨j, a⟩; simp [ctr_generator_mul]
  exact congrArg (fun F => F x) h

/-- Odd product rule for a contraction, with a degree-one left factor. -/
theorem iota_degOne_mul (ι : Module.End ℂ Cochain) (φ : Chain)
    (hgen : ∀ n u, ι (generator n * u) = pairing (generator n) φ • u - generator n * ι u)
    {w : Cochain} (hw : w ∈ degOne) (u : Cochain) :
    ι (w * u) = pairing w φ • u - w * ι u := by
  rw [degOne, Finsupp.supported_eq_span_single] at hw
  induction hw using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨s, hs, rfl⟩ := hv
    obtain ⟨n, rfl⟩ := Finset.card_eq_one.mp hs.out
    exact hgen n u
  | zero => simp
  | add v w _ _ hv hw => simp only [add_mul, map_add, hv, hw, LinearMap.add_apply, add_smul]; abel
  | smul r v _ hv =>
    simp only [smul_mul_assoc, map_smul, hv, LinearMap.smul_apply, smul_sub, smul_smul,
      smul_eq_mul]

/-- The commutator of an even derivation with a contraction. -/
theorem iota_commutator (ι : Module.End ℂ Cochain) (φ φ' : Chain)
    (hone : ι 1 = 0)
    (hgen : ∀ n u, ι (generator n * u) = pairing (generator n) φ • u - generator n * ι u)
    (ι' : Module.End ℂ Cochain) (hone'' : ι' 1 = 0)
    (hgen' : ∀ n u, ι' (generator n * u) = pairing (generator n) φ' • u - generator n * ι' u)
    {E : Module.End ℂ Cochain} (hE : IsEvenGenDer E)
    (hpair : ∀ m, pairing (E (generator m)) φ = -pairing (generator m) φ') (u : Cochain) :
    ι (E u) - E (ι u) = -ι' u := by
  induction u using cochain_induction with
  | hzero => simp
  | hone => rw [← cochain_one_eq, hE.map_one, hone, hone'', map_zero, map_zero]; simp
  | hadd u v hu hv =>
    simp only [map_add]
    rw [neg_add, ← hu, ← hv]; abel
  | hsmul r u hu => simp only [map_smul, ← smul_sub, hu, smul_neg]
  | hgen n u hu =>
    change ι (E (generator n * u)) - E (ι (generator n * u)) = -ι' (generator n * u)
    rw [hE.map_gen_mul, map_add, iota_degOne_mul ι φ hgen (hE.gen_mem n), hgen, hgen,
      hgen', map_sub, map_smul, hE.map_gen_mul, hpair]
    have hu' : ι (E u) = E (ι u) - ι' u := by rw [sub_eq_add_neg, ← hu]; abel
    rw [hu']
    simp only [neg_smul, mul_sub, mul_neg, neg_sub]
    abel

theorem iotaB_commutator {E : Module.End ℂ Cochain} (hE : IsEvenGenDer E) {Db : Module.End ℂ Cur}
    (hB : ∀ x m, pairing (E (generator m)) (phiB x) = -pairing (generator m) (phiB (Db x)))
    (x : Cur) (u : Cochain) : iotaB x (E u) = E (iotaB x u) - iotaB (Db x) u := by
  have h := iota_commutator (iotaB x) (phiB x) (phiB (Db x)) (iotaB_one x) (iotaB_generator_mul x)
    (iotaB (Db x)) (iotaB_one _) (iotaB_generator_mul _) hE (hB x) u
  rw [sub_eq_iff_eq_add] at h
  rw [h]; abel

theorem iotaC_commutator {E : Module.End ℂ Cochain} (hE : IsEvenGenDer E)
    {Dc : Module.End ℂ plus}
    (hC : ∀ x m, pairing (E (generator m)) (phiC x) = -pairing (generator m) (phiC (Dc x)))
    (x : plus) (u : Cochain) : iotaC x (E u) = E (iotaC x u) - iotaC (Dc x) u := by
  have h := iota_commutator (iotaC x) (phiC x) (phiC (Dc x)) (iotaC_one x) (iotaC_generator_mul x)
    (iotaC (Dc x)) (iotaC_one _) (iotaC_generator_mul _) hE (hC x) u
  rw [sub_eq_iff_eq_add] at h
  rw [h]; abel

theorem pairing_algebraMap (u : Cochain) (r : ℂ) :
    pairing u (algebraMap ℂ Chain r) = r * u ∅ := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, pairing_one_right, smul_eq_mul]

/-- Transfer on the coefficient factor `Λ(ε𝔩)`. -/
theorem transfer_coeff {E : Module.End ℂ Cochain} (hE : IsEvenGenDer E) {Db : Module.End ℂ Cur}
    (hB : ∀ x m, pairing (E (generator m)) (phiB x) = -pairing (generator m) (phiB (Db x)))
    (ν : NB) (u : Cochain) :
    pairing (E u) (PhiB ν) = -pairing u (PhiB (derivExt Db ν)) := by
  induction ν using CliffordAlgebra.left_induction generalizing u with
  | algebraMap r =>
    rw [AlgHom.commutes, derivExt_algebraMap, map_zero, map_zero, neg_zero, pairing_algebraMap,
      hE.apply_empty, mul_zero]
  | add ν ν' hν hν' => rw [map_add, map_add, hν, hν', map_add, map_add, map_add, neg_add]
  | ι_mul ν x hν =>
    have hphi : PhiB (ExteriorAlgebra.ι ℂ x * ν) = phiB x * PhiB ν := by
      simp only [map_mul, PhiB_ι]
    have hder : PhiB (derivExt Db (ExteriorAlgebra.ι ℂ x * ν)) =
        phiB (Db x) * PhiB ν + phiB x * PhiB (derivExt Db ν) := by
      rw [derivExt_ι_mul, map_add]
      simp only [map_mul, PhiB_ι]
    rw [hphi, hder, ← pairing_iotaB, iotaB_commutator hE hB, map_sub, LinearMap.sub_apply, hν,
      pairing_iotaB, pairing_iotaB, map_add]
    abel

set_option maxHeartbeats 4000000 in
/-- **Transfer.** An even derivation of cochains whose generator transpose matches
`(Dc, Db)` is minus the transpose of the Lie derivative `lieDeriv Dc (derivExt Db)`. -/
theorem transfer {E : Module.End ℂ Cochain} (hE : IsEvenGenDer E)
    {Dc : Module.End ℂ plus} {Db : Module.End ℂ Cur}
    (hC : ∀ x m, pairing (E (generator m)) (phiC x) = -pairing (generator m) (phiC (Dc x)))
    (hB : ∀ x m, pairing (E (generator m)) (phiB x) = -pairing (generator m) (phiB (Db x)))
    (ξ : GenChains) (u : Cochain) :
    pairing (E u) (Phi ξ) = -pairing u (Phi (lieDeriv Dc (derivExt Db) ξ)) := by
  revert u
  refine chains_induction (k := ℂ) (L := plus) (M := NB)
    (P := fun ξ => ∀ u : Cochain, pairing (E u) (Phi ξ) =
      -pairing u (Phi (lieDeriv Dc (derivExt Db) ξ))) ?_ ?_ ?_ ?_ ξ
  · intro u
    rw [LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero,
      LinearMap.map_zero, neg_zero]
  · intro ν u
    rw [Phi_one_tmul, lieDeriv_tmul, derivExt_one, TensorProduct.zero_tmul, zero_add,
      Phi_one_tmul]
    exact transfer_coeff hE hB ν u
  · intro ξ η hξ hη u
    rw [Phi.map_add, (pairing (E u)).map_add, hξ, hη, (lieDeriv Dc (derivExt Db)).map_add,
      Phi.map_add, (pairing u).map_add, neg_add]
  · intro y ξ hξ u
    rw [Phi_wedgeLeft, ← pairing_iotaC, iotaC_commutator hE hC, pairing.map_sub,
      LinearMap.sub_apply, hξ, pairing_iotaC, pairing_iotaC, lieDeriv_wedgeLeft,
      Phi.map_add, Phi_wedgeLeft, Phi_wedgeLeft, (pairing u).map_add]
    abel

end KhanSL2.Current
