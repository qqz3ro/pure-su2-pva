module

public import KhanSL2.Deformation.Delta
public import KhanSL2.Deformation.Sl2Casimir

@[expose] public section

/-!
# Derivations from generator values; restricted colour actions; the contraction `ι`

* `isOddDer_of_even`, `isEvenDer_of_odd`: `extendDerivation f` is an odd (even) derivation when
  all generator images are even (odd).
* `colorActionOn P e`: the colour action on the generators in a recolouring-stable class `P`,
  zero on the others. `[L^P_a, L^Q_b] = Σ ε_{abc} L^{P ∧ Q}_c` (`colorActionOn_comm`); in
  particular each `L^P` is an `𝔰𝔩₂` action.
* `iota e`: contraction with `b₀ᵉ`, an odd derivation; `[L^P_j, ι_a] = Σ ε_{jad} ι_d` when `P`
  contains the `b₀` modes.
-/

noncomputable section

namespace KhanSL2

open Deformation

/-! ## Derivations from generator values -/

theorem extendDerivation_mul_of_even (f : Mode → Cochain)
    (hf : ∀ m, cochainParity (f m) = f m) (u v : Cochain) :
    extendDerivation f (u * v) = extendDerivation f u * v +
      cochainParity u * extendDerivation f v := by
  apply FiniteExterior.extendDerivation_wedge_twist Mode.code Mode.code_injective f u v
    (cochainParity u)
  intro m
  exact (FiniteExterior.wedge_comm_of_parity_even Mode.code Mode.code_injective
    (f m) (hf m) (cochainParity u)).symm

theorem extendDerivation_mul_of_odd (f : Mode → Cochain)
    (hf : ∀ m, cochainParity (f m) = -f m) (u v : Cochain) :
    extendDerivation f (u * v) = extendDerivation f u * v + u * extendDerivation f v := by
  apply FiniteExterior.extendDerivation_wedge_twist Mode.code Mode.code_injective f u v u
  intro m
  exact (FiniteExterior.wedge_comm_of_parity_odd Mode.code Mode.code_injective
    (f m) (hf m) u).symm

/-- `extendDerivation f` is an odd derivation when the generator images are even. -/
theorem isOddDer_of_even (f : Mode → Cochain) (hf : ∀ m, cochainParity (f m) = f m) :
    IsOddDer (extendDerivation f) where
  mul := extendDerivation_mul_of_even f hf
  parity u := by
    induction u using cochain_induction with
    | hzero => simp
    | hone => rw [cochainParity_one, extendDerivation_one, map_zero, neg_zero]
    | hadd u v hu hv => simp only [map_add, hu, hv, neg_add]
    | hsmul r u hu => simp only [map_smul, hu, smul_neg]
    | hgen m u hu =>
      change extendDerivation f (cochainParity (generator m * u)) =
        -cochainParity (extendDerivation f (generator m * u))
      have e1 : cochainParity (generator m * u) = -(generator m * cochainParity u) := by
        rw [map_mul, cochainParity_generator, neg_mul]
      rw [e1, map_neg, extendDerivation_mul_of_even f hf, extendDerivation_mul_of_even f hf, hu,
        extendDerivation_generator, map_add, map_mul, map_mul, hf, cochainParity_involutive]
      simp only [cochainParity_generator, neg_mul, mul_neg, neg_neg, neg_add]

/-- `extendDerivation f` is an even derivation when the generator images are odd. -/
theorem isEvenDer_of_odd (f : Mode → Cochain) (hf : ∀ m, cochainParity (f m) = -f m) :
    IsEvenDer (extendDerivation f) where
  mul := extendDerivation_mul_of_odd f hf
  parity u := by
    induction u using cochain_induction with
    | hzero => simp
    | hone => rw [cochainParity_one, extendDerivation_one, map_zero]
    | hadd u v hu hv => simp only [map_add, hu, hv]
    | hsmul r u hu => simp only [map_smul, hu]
    | hgen m u hu =>
      change extendDerivation f (cochainParity (generator m * u)) =
        cochainParity (extendDerivation f (generator m * u))
      have e1 : cochainParity (generator m * u) = -(generator m * cochainParity u) := by
        rw [map_mul, cochainParity_generator, neg_mul]
      rw [e1, map_neg, extendDerivation_mul_of_odd f hf, extendDerivation_mul_of_odd f hf, hu,
        extendDerivation_generator, map_add, map_mul, map_mul, hf]
      simp only [cochainParity_generator, neg_mul, mul_neg, neg_neg, neg_add]

/-! ## Classes of generators -/

/-- The modes `b₀ᵃ`. -/
def Mode.isB0 : Mode → Bool
  | .b 0 _ => true
  | _ => false

/-- The modes `b_{j+1}ᵃ`. -/
def Mode.isZ : Mode → Bool
  | .b (_ + 1) _ => true
  | _ => false

/-- The `b` modes. -/
def Mode.isB : Mode → Bool
  | .b _ _ => true
  | _ => false

/-- The `c` modes. -/
def Mode.isC : Mode → Bool
  | .c _ _ => true
  | _ => false

/-- A class of modes closed under recolouring. -/
def ColorStable (P : Mode → Bool) : Prop := ∀ m c, P (m.recolor c) = P m

theorem colorStable_isB0 : ColorStable Mode.isB0 := by
  intro m c; cases m with
  | b j a => cases j <;> rfl
  | c j a => rfl

theorem colorStable_isZ : ColorStable Mode.isZ := by
  intro m c; cases m with
  | b j a => cases j <;> rfl
  | c j a => rfl

theorem colorStable_isB : ColorStable Mode.isB := by intro m c; cases m <;> rfl

theorem colorStable_isC : ColorStable Mode.isC := by intro m c; cases m <;> rfl

theorem colorStable_true : ColorStable (fun _ => true) := fun _ _ => rfl

theorem ColorStable.and {P Q : Mode → Bool} (hP : ColorStable P) (hQ : ColorStable Q) :
    ColorStable (fun m => P m && Q m) := by
  intro m c; simp only [hP m c, hQ m c]

/-! ## Restricted colour actions -/

/-- The colour action on the generators in `P`. -/
def colorActionOn (P : Mode → Bool) (e : Fin 3) : Cochain →ₗ[ℂ] Cochain :=
  extendDerivation (fun m => if P m then colorGenerator e m else 0)

theorem colorActionOn_generator (P : Mode → Bool) (e : Fin 3) (m : Mode) :
    colorActionOn P e (generator m) = if P m then colorGenerator e m else 0 :=
  extendDerivation_generator _ m

theorem colorGenerator_parity' (e : Fin 3) (m : Mode) :
    cochainParity (colorGenerator e m) = -colorGenerator e m := by
  simp [colorGenerator, map_sum, map_smul]

theorem isEvenDer_colorActionOn (P : Mode → Bool) (e : Fin 3) :
    IsEvenDer (colorActionOn P e) :=
  isEvenDer_of_odd _ (fun m => by
    split_ifs
    · exact colorGenerator_parity' e m
    · simp)

theorem colorActionOn_true (e : Fin 3) : colorActionOn (fun _ => true) e = colorAction e := rfl

/-- Restricted colour actions add over a disjoint splitting of the modes. -/
theorem colorActionOn_add {P Q R : Mode → Bool} (h : ∀ m, R m = (P m || Q m))
    (hPQ : ∀ m, ¬ (P m ∧ Q m)) (e : Fin 3) :
    colorActionOn R e = colorActionOn P e + colorActionOn Q e := by
  apply (isEvenDer_colorActionOn R e).ext ((isEvenDer_colorActionOn P e).add
    (isEvenDer_colorActionOn Q e))
  intro m
  simp only [LinearMap.add_apply, colorActionOn_generator, h m]
  cases hp : P m <;> cases hq : Q m <;> simp_all

/-- The structure-constant identity behind `[L_a, L_b] = Σ ε_{abc} L_c` on generators. -/
theorem epsilon_comm_identity (a b x f : Fin 3) :
    (∑ d : Fin 3, (epsilon b x d * epsilon a d f - epsilon a x d * epsilon b d f)) =
      ∑ c : Fin 3, epsilon a b c * epsilon c x f := by
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases f <;>
    norm_num [epsilon, Fin.sum_univ_three]

theorem Mode.color_recolor (m : Mode) (c : Fin 3) : (m.recolor c).color = c := by
  cases m <;> rfl

theorem Mode.recolor_recolor (m : Mode) (c d : Fin 3) : (m.recolor c).recolor d = m.recolor d := by
  cases m <;> rfl

theorem colorAction_colorGenerator (a e : Fin 3) (m : Mode) :
    colorAction a (colorGenerator e m) =
      ∑ f : Fin 3, (∑ d : Fin 3, epsilon e m.color d * epsilon a d f) • generator (m.recolor f) := by
  simp only [colorGenerator, map_sum, map_smul, colorAction_generator, Mode.color_recolor,
    Mode.recolor_recolor, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro f _
  rw [Finset.sum_smul]

theorem colorActionOn_colorGenerator {P : Mode → Bool} (hP : ColorStable P) (a e : Fin 3)
    (m : Mode) : colorActionOn P a (colorGenerator e m) =
      if P m then colorAction a (colorGenerator e m) else 0 := by
  simp only [colorGenerator, map_sum, map_smul, colorActionOn_generator, colorAction_generator,
    hP m]
  split_ifs <;> simp

/-- The colour action relation on generators. -/
theorem colorAction_comm_generator (a b : Fin 3) (m : Mode) :
    colorAction a (colorGenerator b m) - colorAction b (colorGenerator a m) =
      ∑ c : Fin 3, epsilon a b c • colorGenerator c m := by
  rw [colorAction_colorGenerator, colorAction_colorGenerator, ← Finset.sum_sub_distrib]
  simp only [← sub_smul, colorGenerator, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro f _
  rw [← Finset.sum_smul, ← epsilon_comm_identity, Finset.sum_sub_distrib]

/-- **Commutators of restricted colour actions.** -/
theorem colorActionOn_comm {P Q : Mode → Bool} (hP : ColorStable P) (hQ : ColorStable Q)
    (a b : Fin 3) (u : Cochain) :
    colorActionOn P a (colorActionOn Q b u) - colorActionOn Q b (colorActionOn P a u) =
      ∑ c : Fin 3, epsilon a b c • colorActionOn (fun m => P m && Q m) c u := by
  have h := (isEvenDer_colorActionOn P a).commutator (isEvenDer_colorActionOn Q b)
  have hR : IsEvenDer (∑ c : Fin 3, epsilon a b c • colorActionOn (fun m => P m && Q m) c) := by
    simp only [Fin.sum_univ_three]
    exact (((isEvenDer_colorActionOn _ 0).smul _).add ((isEvenDer_colorActionOn _ 1).smul _)).add
      ((isEvenDer_colorActionOn _ 2).smul _)
  have := h.ext hR (fun m => by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, colorActionOn_generator,
      LinearMap.sum_apply, LinearMap.smul_apply]
    by_cases hPm : P m <;> by_cases hQm : Q m
    · simp only [hPm, hQm, if_true, Bool.and_self, colorActionOn_colorGenerator hP,
        colorActionOn_colorGenerator hQ]
      exact colorAction_comm_generator a b m
    · simp [hPm, hQm, colorActionOn_colorGenerator hP, colorActionOn_colorGenerator hQ]
    · simp [hPm, hQm, colorActionOn_colorGenerator hP, colorActionOn_colorGenerator hQ]
    · simp [hPm, hQm])
  exact LinearMap.congr_fun this u

theorem isColorAction_colorActionOn {P : Mode → Bool} (hP : ColorStable P) :
    IsColorAction (colorActionOn P) := by
  intro a b
  apply LinearMap.ext
  intro u
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
    LinearMap.smul_apply]
  rw [colorActionOn_comm hP hP]
  simp

end KhanSL2
