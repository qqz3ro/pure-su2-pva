module

public import KhanSL2.Chains.Comparison.Generators
public import KhanSL2.Chains.Comparison.Support

@[expose] public section

/-!
# `Phi` intertwines boundaries and the `𝔤`-actions

* `Phi (relTheta a ξ) = - coaction a (Phi ξ)`;
* `Phi (boundary ξ) = boundary (Phi ξ)`.

The general CE boundary on `Λ𝔩₊ ⊗ Λ(ε𝔩)` is the graded transpose of `q`.
-/

noncomputable section

open scoped TensorProduct

namespace KhanSL2.Current

open LieChains FiniteExterior

/-! ## Brackets of basis elements -/

theorem relD_plusCur (a : Fin 3) (i : ℕ) (b : Fin 3) :
    relD a (plusCur i b) = ∑ c : Fin 3, epsilon a b c • plusCur i c := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  change ⁅cur 0 a, cur (i + 1) b⁆ = _
  rw [lie_cur_cur, zero_add]
  rfl

theorem adCur_cur (y : Cur) (x : Cur) : adCur y x = ⁅y, x⁆ := rfl

theorem adCur_cur_cur (n : ℕ) (a : Fin 3) (i : ℕ) (b : Fin 3) :
    adCur (cur n a) (cur i b) = ∑ c : Fin 3, epsilon a b c • cur (n + i) c := by
  rw [adCur_cur]
  exact lie_cur_cur n i a b

theorem adPlus_plusCur (j : ℕ) (a : Fin 3) (i : ℕ) (b : Fin 3) :
    LieModule.toEnd ℂ plus plus (plusCur j a) (plusCur i b) =
      ∑ c : Fin 3, epsilon a b c • plusCur (i + j + 1) c := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  change ⁅cur (j + 1) a, cur (i + 1) b⁆ = _
  rw [lie_cur_cur]
  apply Finset.sum_congr rfl
  intro c _
  change _ = epsilon a b c • cur (i + j + 1 + 1) c
  congr 2
  omega

/-! ## Even derivations -/

theorem colorAction_one (a : Fin 3) : colorAction a 1 = 0 := by
  have h := colorAction_mul a 1 1
  rw [one_mul, one_mul, mul_one] at h
  have : colorAction a 1 + colorAction a 1 - colorAction a 1 = 0 := by rw [← h]; abel
  simpa using this

theorem colorAction_generator (a : Fin 3) (m : Mode) :
    colorAction a (generator m) = colorGenerator a m := by
  simp only [colorAction, extendDerivation, generator, Finsupp.linearCombination_single,
    one_smul, Finset.sum_singleton, Finset.erase_singleton]
  have hpos : ({x ∈ ({m} : Finset Mode) | x.code < m.code}).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx; rw [Finset.mem_singleton.mp hx]; exact lt_irrefl _
  rw [position, hpos, pow_zero, one_smul]
  exact wedge_cochainOne _

theorem colorGenerator_mem_degOne (a : Fin 3) (m : Mode) : colorGenerator a m ∈ degOne :=
  Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (generator_mem_degOne _)

theorem colorAction_isEvenGenDer (a : Fin 3) : IsEvenGenDer (colorAction a) where
  map_one := colorAction_one a
  map_gen_mul m u := by
    rw [colorAction_mul]
  gen_mem m := by rw [colorAction_generator]; exact colorGenerator_mem_degOne a m

theorem colorAction_hC (a : Fin 3) (x : plus) (m : Mode) :
    pairing (colorAction a (generator m)) (phiC x) = -pairing (generator m) (phiC (relD a x)) := by
  have h : (pairing (colorAction a (generator m))) ∘ₗ phiC =
      -((pairing (generator m)) ∘ₗ phiC ∘ₗ relD a) := by
    apply plusBasis.ext
    rintro ⟨i, b⟩
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, plusBasis_apply, phiC_plusCur,
      relD_plusCur, map_sum, map_smul, colorAction_generator, pairing_colorGenerator_c,
      smul_eq_mul]
  exact congrArg (fun F => F x) h

theorem colorAction_hB (a : Fin 3) (x : Cur) (m : Mode) :
    pairing (colorAction a (generator m)) (phiB x) =
      -pairing (generator m) (phiB (adCur (cur 0 a) x)) := by
  have h : (pairing (colorAction a (generator m))) ∘ₗ phiB =
      -((pairing (generator m)) ∘ₗ phiB ∘ₗ adCur (cur 0 a)) := by
    apply curBasis.ext
    rintro ⟨i, b⟩
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, curBasis_apply, phiB_cur,
      adCur_cur_cur, zero_add, map_sum, map_smul, colorAction_generator,
      pairing_colorGenerator_b, smul_eq_mul]
  exact congrArg (fun F => F x) h

theorem relS_eq (a : Fin 3) : relS a = derivExt (adCur (cur 0 a)) := LinearMap.ext fun _ => rfl

set_option maxHeartbeats 1000000 in
theorem pairing_colorAction_Phi (a : Fin 3) (ξ : GenChains) (u : Cochain) :
    pairing (colorAction a u) (Phi ξ) = -pairing u (Phi (relTheta a ξ)) := by
  rw [relTheta, relS_eq]
  exact transfer (colorAction_isEvenGenDer a) (colorAction_hC a) (colorAction_hB a) ξ u

/-- `Phi` turns the relative action of `t_a` into minus the color coaction. -/
theorem Phi_relTheta (a : Fin 3) (ξ : GenChains) :
    Phi (relTheta a ξ) = -coaction a (Phi ξ) := by
  apply chain_ext
  intro u
  rw [map_neg, ← pairing_colorAction, pairing_colorAction_Phi, neg_neg]

end KhanSL2.Current
