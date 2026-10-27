module

public import KhanSL2.Chains.Comparison.Intertwine

@[expose] public section

/-!
# `Phi` intertwines the CE boundaries

The general boundary of `Λ𝔩₊ ⊗ Λ(ε𝔩)` corresponds under `Phi` to the graded transpose
of `q`. The induction step uses Cartan's formula on cochains:
`ι_y q + q ι_y` is an even derivation whose transpose is minus the Lie derivative by `y`.
-/

noncomputable section

open scoped TensorProduct

namespace KhanSL2.Current

open LieChains FiniteExterior

theorem q_one : q 1 = 0 := by
  have h := q_mul 1 1
  simp only [one_mul, mul_one, map_one] at h
  have : q 1 + q 1 - q 1 = 0 := by rw [← h]; abel
  simpa using this

theorem q_generator (m : Mode) : q (generator m) = qGenerator m := by
  simp only [q, extendDerivation, generator, Finsupp.linearCombination_single,
    one_smul, Finset.sum_singleton, Finset.erase_singleton]
  have hpos : ({x ∈ ({m} : Finset Mode) | x.code < m.code}).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx; rw [Finset.mem_singleton.mp hx]; exact lt_irrefl _
  rw [position, hpos, pow_zero, one_smul]
  exact wedge_cochainOne _

/-- The odd product rule for contractions by `𝔩₊`. -/
theorem iotaC_mul (y : plus) (w u : Cochain) :
    iotaC y (w * u) = iotaC y w * u + cochainParity w * iotaC y u := by
  have h : (LinearMap.applyₗ (w * u)) ∘ₗ iotaC =
      (LinearMap.mulRight ℂ u) ∘ₗ (LinearMap.applyₗ w) ∘ₗ iotaC +
        (LinearMap.mulLeft ℂ (cochainParity w)) ∘ₗ (LinearMap.applyₗ u) ∘ₗ iotaC := by
    apply plusBasis.ext
    rintro ⟨j, a⟩
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.applyₗ_apply_apply,
      plusBasis_apply, iotaC_plusCur, LinearMap.mulRight_apply, LinearMap.mulLeft_apply]
    exact contraction_wedge GeneratorOrder.code GeneratorOrder.code_injective _ w u
  exact congrArg (fun F => F y) h

theorem iotaC_generator (y : plus) (m : Mode) :
    iotaC y (generator m) = pairing (generator m) (phiC y) • (1 : Cochain) := by
  have h := iotaC_generator_mul y m 1
  rw [mul_one, iotaC_one, mul_zero, sub_zero] at h
  exact h

/-- Contractions lower the exterior degree by one. -/
theorem ctr_mem_card {n : ℕ} {w : Cochain}
    (hw : w ∈ Finsupp.supported ℂ ℂ {s : ExteriorMonomial | s.card = n + 1}) (m : Mode) :
    ctr m w ∈ Finsupp.supported ℂ ℂ {s : ExteriorMonomial | s.card = n} := by
  rw [Finsupp.supported_eq_span_single] at hw
  induction hw using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨s, hs, rfl⟩ := hv
    change contraction _ m (monomial s) ∈ _
    rw [contraction_monomial]
    split_ifs with hms
    · apply Submodule.smul_mem
      apply Finsupp.single_mem_supported
      change (s.erase m).card = n
      rw [Finset.card_erase_of_mem hms, hs.out]; rfl
    · exact Submodule.zero_mem _
  | zero => simp
  | add v w _ _ hv hw => rw [map_add]; exact Submodule.add_mem _ hv hw
  | smul r v _ hv => rw [map_smul]; exact Submodule.smul_mem _ _ hv

theorem iotaC_mem_degOne (y : plus) {w : Cochain}
    (hw : w ∈ Finsupp.supported ℂ ℂ {s : ExteriorMonomial | s.card = 2}) :
    iotaC y w ∈ degOne := by
  rw [iotaC, Module.Basis.constr_apply, Finsupp.sum, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun p _ => by
    rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (ctr_mem_card (n := 1) hw _)

theorem qGenerator_mem_card_two (m : Mode) :
    qGenerator m ∈ Finsupp.supported ℂ ℂ {s : ExteriorMonomial | s.card = 2} := by
  intro s hs
  have h := qGenerator_degree m hs
  change monomialDegree s = _ at h
  simp only [monomialDegree, Prod.mk.injEq] at h
  change s.card = 2
  exact_mod_cast h.1

/-- Cartan's operator `ι_y q + q ι_y`. -/
def lieC (y : plus) : Module.End ℂ Cochain := iotaC y ∘ₗ q + q ∘ₗ iotaC y

theorem lieC_apply (y : plus) (u : Cochain) : lieC y u = iotaC y (q u) + q (iotaC y u) := rfl

theorem lieC_generator (y : plus) (m : Mode) : lieC y (generator m) = iotaC y (qGenerator m) := by
  rw [lieC_apply, q_generator, iotaC_generator, map_smul, q_one, smul_zero, add_zero]

theorem lieC_isEvenGenDer (y : plus) : IsEvenGenDer (lieC y) where
  map_one := by rw [lieC_apply, q_one, map_zero, iotaC_one, map_zero, add_zero]
  map_gen_mul m u := by
    rw [lieC_generator, lieC_apply, lieC_apply, q_mul, q_generator, cochainParity_generator,
      map_add, iotaC_mul, qGenerator_parity, neg_mul, map_neg, iotaC_generator_mul,
      iotaC_generator_mul, map_sub, map_smul, q_mul, q_generator, cochainParity_generator]
    simp only [neg_mul, mul_add, smul_sub, sub_neg_eq_add]
    abel
  gen_mem m := by
    rw [lieC_generator]
    exact iotaC_mem_degOne y (qGenerator_mem_card_two m)

theorem lieC_hC (y : plus) (x : plus) (m : Mode) :
    pairing (lieC y (generator m)) (phiC x) =
      -pairing (generator m) (phiC (LieModule.toEnd ℂ plus plus y x)) := by
  rw [lieC_generator]
  have h : ((pairing.compl₂ phiC) ∘ₗ (LinearMap.applyₗ (qGenerator m)) ∘ₗ iotaC) =
      -((LieModule.toEnd ℂ plus plus : plus →ₗ[ℂ] Module.End ℂ plus).compr₂
        (pairing (generator m) ∘ₗ phiC)) := by
    apply plusBasis.ext
    rintro ⟨j, a⟩
    apply plusBasis.ext
    rintro ⟨i, b⟩
    simp only [LinearMap.comp_apply, LinearMap.compl₂_apply, LinearMap.applyₗ_apply_apply,
      LinearMap.neg_apply, LinearMap.compr₂_apply, plusBasis_apply, iotaC_plusCur,
      phiC_plusCur, LieHom.coe_toLinearMap, adPlus_plusCur, map_sum, map_smul, smul_eq_mul]
    rw [pairing_ctr, pairing_qGenerator_cc]
  exact congrArg (fun F => F y x) h

theorem lieC_hB (y : plus) (x : Cur) (m : Mode) :
    pairing (lieC y (generator m)) (phiB x) =
      -pairing (generator m) (phiB (adCur (y : Cur) x)) := by
  rw [lieC_generator]
  have h : ((pairing.compl₂ phiB) ∘ₗ (LinearMap.applyₗ (qGenerator m)) ∘ₗ iotaC) =
      -(((LieModule.toEnd ℂ Cur Cur : Cur →ₗ[ℂ] Module.End ℂ Cur) ∘ₗ
        (plus : Submodule ℂ Cur).subtype).compr₂ (pairing (generator m) ∘ₗ phiB)) := by
    apply plusBasis.ext
    rintro ⟨j, a⟩
    apply curBasis.ext
    rintro ⟨i, b⟩
    simp only [LinearMap.comp_apply, LinearMap.compl₂_apply, LinearMap.applyₗ_apply_apply,
      LinearMap.neg_apply, LinearMap.compr₂_apply, plusBasis_apply, curBasis_apply,
      iotaC_plusCur, phiB_cur, Submodule.subtype_apply, LieHom.coe_toLinearMap]
    rw [pairing_ctr, pairing_qGenerator_cb]
    change _ = -(pairing (generator m)) (phiB (adCur (cur (j + 1) a) (cur i b)))
    rw [adCur_cur_cur, map_sum, map_sum]
    simp only [map_smul, phiB_cur, smul_eq_mul]
    congr 2
    funext c
    congr 4
    omega
  exact congrArg (fun F => F y x) h

theorem theta_eq (y : plus) :
    theta NB y = lieDeriv (LieModule.toEnd ℂ plus plus y) (derivExt (adCur (y : Cur))) := by
  rw [theta]
  congr 1

set_option maxHeartbeats 1000000 in
theorem pairing_lieC_Phi (y : plus) (ξ : GenChains) (u : Cochain) :
    pairing (lieC y u) (Phi ξ) = -pairing u (Phi (theta NB y ξ)) := by
  rw [theta_eq]
  exact transfer (lieC_isEvenGenDer y) (lieC_hC y) (lieC_hB y) ξ u

set_option maxHeartbeats 4000000 in
/-- The general CE boundary is the graded transpose of `q`, through `Phi`. -/
theorem pairing_q_Phi (ξ : GenChains) (u : Cochain) :
    pairing (q u) (Phi ξ) = pairing u (Phi (LieChains.boundary NB ξ)) := by
  revert u
  refine chains_induction (k := ℂ) (L := plus) (M := NB)
    (P := fun ξ => ∀ u : Cochain,
      pairing (q u) (Phi ξ) = pairing u (Phi (LieChains.boundary NB ξ))) ?_ ?_ ?_ ?_ ξ
  · intro u
    rw [LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero,
      LinearMap.map_zero]
  · intro ν u
    rw [Phi_one_tmul, boundary_one_tmul, LinearMap.map_zero, LinearMap.map_zero, pairing_q_PhiB]
  · intro ξ η hξ hη u
    rw [Phi.map_add, (pairing (q u)).map_add, hξ, hη, (LieChains.boundary NB).map_add,
      Phi.map_add, (pairing u).map_add]
  · intro y ξ hξ u
    have hc := pairing_lieC_Phi y ξ u
    rw [lieC_apply, pairing.map_add, LinearMap.add_apply] at hc
    rw [Phi_wedgeLeft, ← pairing_iotaC, boundary_wedgeLeft, Phi.map_sub, Phi.map_neg,
      Phi_wedgeLeft, (pairing u).map_sub, (pairing u).map_neg, ← pairing_iotaC, ← hξ, ← hc]
    abel

/-- **`Phi` is a chain map.** -/
theorem Phi_boundary (ξ : GenChains) :
    Phi (LieChains.boundary NB ξ) = KhanSL2.boundary (Phi ξ) := by
  apply chain_ext
  intro u
  rw [← pairing_q_Phi, KhanSL2.pairing_q]

end KhanSL2.Current
