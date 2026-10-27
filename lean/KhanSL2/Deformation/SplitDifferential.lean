module

public import KhanSL2.Deformation.SplitOps
public import KhanSL2.Deformation.RelabelOne

@[expose] public section

/-!
# The split differential `D''` and its pieces (blueprint `lem:D0split`, `lem:Hlpos`)

* `dpp` (`D''`): `c_j ↦ Q c_j`, `b_j ↦ -½ Σ_{i+k=j} ε b_i b_k`;
* `dC`: `Q` on the `c` modes; `dZ`: the `𝔩₊` differential on the `b_{≥1}` modes;
  `dG`: the `𝔤` differential on the `b₀` modes; `coupling = Σ_e b₀ᵉ L^Z_e`.

Main identities: `dpp = dC + dZ + dG + coupling` (`dpp_eq`), the Cartan formulas
`[D'', ι_e] = L^B_e` (`dpp_iota`) and `[dG, ι_e] = L^{B₀}_e` (`dG_iota`),
`Σ_e b₀ᵉ L^{B₀}_e = 2 dG` (`b0_LB0_eq`), and the equivariances.
-/

noncomputable section

namespace KhanSL2

open Deformation

/-! ## Colour actions on the classes of modes -/

/-- The colour action on the `b` modes. -/
abbrev LB (e : Fin 3) : Cochain →ₗ[ℂ] Cochain := colorActionOn Mode.isB e
/-- The colour action on the `b₀` modes. -/
abbrev LB0 (e : Fin 3) : Cochain →ₗ[ℂ] Cochain := colorActionOn Mode.isB0 e
/-- The colour action on the `b_{≥1}` modes. -/
abbrev LZ (e : Fin 3) : Cochain →ₗ[ℂ] Cochain := colorActionOn Mode.isZ e
/-- The colour action on the `c` modes. -/
abbrev LC (e : Fin 3) : Cochain →ₗ[ℂ] Cochain := colorActionOn Mode.isC e

theorem LB_eq (e : Fin 3) : LB e = LB0 e + LZ e :=
  colorActionOn_add (fun m => by cases m with | b j a => cases j <;> rfl | c j a => rfl)
    (fun m => by cases m with | b j a => cases j <;> simp [Mode.isB0, Mode.isZ] | c j a => simp [Mode.isB0]) e

theorem colorAction_eq_LC_LB (e : Fin 3) : colorAction e = LC e + LB e := by
  rw [← colorActionOn_true]
  exact colorActionOn_add (fun m => by cases m <;> rfl)
    (fun m => by cases m <;> simp [Mode.isC, Mode.isB]) e

/-- A restricted colour action kills products of generators outside its class. -/
theorem colorActionOn_mul_of_not {P : Mode → Bool} (e : Fin 3) {m m' : Mode} (hm : P m = false)
    (hm' : P m' = false) : colorActionOn P e (generator m * generator m') = 0 := by
  rw [(isEvenDer_colorActionOn P e).mul, colorActionOn_generator, colorActionOn_generator, hm, hm']
  simp

/-- A restricted colour action agrees with the full one on products inside its class. -/
theorem colorActionOn_mul_of {P : Mode → Bool} (e : Fin 3) {m m' : Mode}
    (hm : P m = true) (hm' : P m' = true) :
    colorActionOn P e (generator m * generator m') = colorAction e (generator m * generator m') := by
  rw [(isEvenDer_colorActionOn P e).mul, colorActionOn_generator, colorActionOn_generator, hm,
    hm', colorAction_mul, colorAction_generator, colorAction_generator]
  simp

/-! ## Convolutions -/

/-- `Σ_{i+k=j+1, i,k ≥ 1} ε b_i b_k`. -/
def zzConv (j : ℕ) (a : Fin 3) : Cochain := ∑ i ∈ Finset.range j, bbPair (i + 1) (j - i) a

theorem bbPair_parity (i k : ℕ) (a : Fin 3) : cochainParity (bbPair i k a) = bbPair i k a := by
  simpa [koszulSign] using cochainParity_of_mem (bbPair_mem i k a)

theorem zzConv_parity (j : ℕ) (a : Fin 3) : cochainParity (zzConv j a) = zzConv j a := by
  simp [zzConv, map_sum, bbPair_parity]

theorem bbPair_swap (i k : ℕ) (a : Fin 3) : bbPair k i a = bbPair i k a := by
  simp only [bbPair]
  exact epsilon_pair_swap a (fun b => .b k b) (fun c => .b i c)

/-- `Σ_{i+k=j+1} = Σ_{i,k ≥ 1} + 2 (b₀, b_{j+1})`. -/
theorem bbConv_succ (j : ℕ) (a : Fin 3) :
    bbConv (j + 1) a = zzConv j a + (2 : ℂ) • bbPair 0 (j + 1) a := by
  rw [bbConv, Finset.sum_range_succ, Finset.sum_range_succ', zzConv]
  simp only [Nat.sub_self, Nat.sub_zero]
  rw [bbPair_swap, two_smul]
  have h : ∀ i ∈ Finset.range j, bbPair (i + 1) (j + 1 - (i + 1)) a = bbPair (i + 1) (j - i) a := by
    intro i _; congr 1; omega
  rw [Finset.sum_congr rfl h]
  abel

theorem colorActionOn_bbPair {P : Mode → Bool} (e : Fin 3) {i k : ℕ}
    (hi : ∀ x, P (.b i x) = true) (hk : ∀ x, P (.b k x) = true) (a : Fin 3) :
    colorActionOn P e (bbPair i k a) = ∑ f : Fin 3, epsilon e a f • bbPair i k f := by
  rw [← colorAction_bbPair]
  simp only [bbPair, map_sum, map_smul, ← cochain_mul_eq_wedge]
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  rw [colorActionOn_mul_of e (hi b) (hk c)]

/-! ## The operators -/

def dppGen : Mode → Cochain
  | .c j a => qGenerator (.c j a)
  | .b j a => (-(1 / 2 : ℂ)) • bbConv j a

/-- **`D''`**, the Chevalley–Eilenberg differential of `𝔥 = 𝔩₊ ⊕ 𝔩` in split coordinates. -/
def dpp : Cochain →ₗ[ℂ] Cochain := extendDerivation dppGen

def dCGen : Mode → Cochain
  | .c j a => qGenerator (.c j a)
  | .b _ _ => 0

def dZGen : Mode → Cochain
  | .b (j + 1) a => (-(1 / 2 : ℂ)) • zzConv j a
  | _ => 0

def dGGen : Mode → Cochain
  | .b 0 a => (-(1 / 2 : ℂ)) • bbPair 0 0 a
  | _ => 0

/-- `Q` on the `c` modes. -/
def dC : Cochain →ₗ[ℂ] Cochain := extendDerivation dCGen
/-- The differential of `𝔩₊` on the `b_{≥1}` modes. -/
def dZ : Cochain →ₗ[ℂ] Cochain := extendDerivation dZGen
/-- The differential of `𝔤` on the `b₀` modes. -/
def dG : Cochain →ₗ[ℂ] Cochain := extendDerivation dGGen

theorem isOddDer_dpp : IsOddDer dpp :=
  isOddDer_of_even _ (fun m => by
    cases m with
    | c j a => exact qGenerator_parity _
    | b j a => simp only [dppGen, map_smul, bbConv_parity])

theorem isOddDer_dC : IsOddDer dC :=
  isOddDer_of_even _ (fun m => by
    cases m with
    | c j a => exact qGenerator_parity _
    | b j a => simp [dCGen])

theorem isOddDer_dZ : IsOddDer dZ :=
  isOddDer_of_even _ (fun m => by
    cases m with
    | c j a => simp [dZGen]
    | b j a => cases j with
      | zero => simp [dZGen]
      | succ j => simp only [dZGen, map_smul, zzConv_parity])

theorem isOddDer_dG : IsOddDer dG :=
  isOddDer_of_even _ (fun m => by
    cases m with
    | c j a => simp [dGGen]
    | b j a => cases j with
      | zero => simp only [dGGen, map_smul, bbPair_parity]
      | succ j => simp [dGGen])

@[simp] theorem dpp_generator (m : Mode) : dpp (generator m) = dppGen m :=
  extendDerivation_generator _ m
@[simp] theorem dC_generator (m : Mode) : dC (generator m) = dCGen m :=
  extendDerivation_generator _ m
@[simp] theorem dZ_generator (m : Mode) : dZ (generator m) = dZGen m :=
  extendDerivation_generator _ m
@[simp] theorem dG_generator (m : Mode) : dG (generator m) = dGGen m :=
  extendDerivation_generator _ m

/-- Left multiplication by a generator, composed with an even derivation, is odd. -/
theorem isOddDer_mulLeft (m : Mode) {E : Cochain →ₗ[ℂ] Cochain} (hE : IsEvenDer E) :
    IsOddDer (LinearMap.mulLeft ℂ (generator m) ∘ₗ E) where
  mul u v := by
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, hE.mul, mul_add, ← mul_assoc]
    congr 1
    rw [show generator m * u = cochainParity u * generator m from
      FiniteExterior.wedge_generator_supercomm Mode.code Mode.code_injective m u]
  parity u := by
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, hE.parity, map_mul,
      cochainParity_generator, neg_mul, neg_neg]

/-- The coupling `Σ_e b₀ᵉ L^Z_e`. -/
def coupling : Cochain →ₗ[ℂ] Cochain :=
  ∑ e : Fin 3, LinearMap.mulLeft ℂ (generator (.b 0 e)) ∘ₗ LZ e

theorem isOddDer_sum3 {D : Fin 3 → Cochain →ₗ[ℂ] Cochain} (h : ∀ e, IsOddDer (D e)) :
    IsOddDer (∑ e : Fin 3, D e) := by
  simp only [Fin.sum_univ_three]
  exact ((h 0).add (h 1)).add (h 2)

theorem isEvenDer_sum3 {D : Fin 3 → Cochain →ₗ[ℂ] Cochain} (h : ∀ e, IsEvenDer (D e)) :
    IsEvenDer (∑ e : Fin 3, D e) := by
  simp only [Fin.sum_univ_three]
  exact ((h 0).add (h 1)).add (h 2)

theorem isOddDer_coupling : IsOddDer coupling :=
  isOddDer_sum3 (fun e => isOddDer_mulLeft _ (isEvenDer_colorActionOn _ e))

theorem coupling_generator (m : Mode) :
    coupling (generator m) = ∑ e : Fin 3, generator (.b 0 e) * LZ e (generator m) := by
  simp [coupling, LinearMap.sum_apply]

/-! ## `D'' = d_c + d_Z + d_g + coupling` -/

theorem sum_b0_colorGenerator (j : ℕ) (a : Fin 3) :
    (∑ e : Fin 3, generator (.b 0 e) * colorGenerator e (.b j a)) = -bbPair 0 j a := by
  simp only [colorGenerator, Mode.color, Mode.recolor, Finset.mul_sum, mul_smul_comm, bbPair,
    ← Finset.sum_neg_distrib, cochain_mul_eq_wedge]
  apply Finset.sum_congr rfl; intro e _
  apply Finset.sum_congr rfl; intro c _
  rw [epsilon_swap_left, neg_smul]

theorem dpp_eq : dpp = dC + dZ + dG + coupling := by
  apply isOddDer_dpp.ext (((isOddDer_dC.add isOddDer_dZ).add isOddDer_dG).add isOddDer_coupling)
  intro m
  simp only [LinearMap.add_apply, dpp_generator, dC_generator, dZ_generator, dG_generator,
    coupling_generator, colorActionOn_generator]
  cases m with
  | c j a => simp [dppGen, dCGen, dZGen, dGGen, Mode.isZ]
  | b j a =>
    cases j with
    | zero =>
      simp [dppGen, dCGen, dZGen, dGGen, Mode.isZ, bbConv]
    | succ j =>
      simp only [dppGen, dCGen, dZGen, dGGen, Mode.isZ, if_true, bbConv_succ,
        sum_b0_colorGenerator, smul_add, zero_add, add_zero, smul_smul]
      norm_num

/-- `Σ_e b₀ᵉ L^{B₀}_e = 2 d_g`. -/
theorem b0_LB0_eq :
    (∑ e : Fin 3, LinearMap.mulLeft ℂ (generator (.b 0 e)) ∘ₗ LB0 e) = (2 : ℂ) • dG := by
  apply (isOddDer_sum3 (fun e => isOddDer_mulLeft _ (isEvenDer_colorActionOn _ e))).ext
    (isOddDer_dG.smul 2)
  intro m
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    colorActionOn_generator, LinearMap.smul_apply, dG_generator]
  cases m with
  | c j a => simp [Mode.isB0, dGGen]
  | b j a =>
    cases j with
    | zero =>
      simp only [Mode.isB0, if_true, dGGen, smul_smul]
      rw [sum_b0_colorGenerator]
      norm_num
    | succ j => simp [Mode.isB0, dGGen]

/-! ## Cartan formulas -/

theorem iota_cochainOne (e : Fin 3) : iota e cochainOne = 0 := (isOddDer_iota e).map_one

theorem dpp_one : dpp cochainOne = 0 := isOddDer_dpp.map_one

/-- **`[D'', ι_e] = L^B_e`.** -/
theorem dpp_iota (e : Fin 3) (v : Cochain) : dpp (iota e v) + iota e (dpp v) = LB e v := by
  have h := isOddDer_dpp.anticommutator (isOddDer_iota e)
  have := h.ext (isEvenDer_colorActionOn Mode.isB e) (fun m => by
    simp only [LinearMap.add_apply, LinearMap.comp_apply, iota_generator, dpp_generator,
      colorActionOn_generator]
    cases m with
    | c j a => simp [dppGen, Mode.isB, iota_qGenerator]
    | b j a =>
      simp only [dppGen, Mode.isB, if_true, map_smul, iota_bbConv, smul_smul, colorGenerator,
        Mode.color, Mode.recolor, Finset.smul_sum]
      split_ifs <;> simp only [map_zero, dpp_one, zero_add] <;>
      · apply Finset.sum_congr rfl; intro c _
        rw [epsilon_swap_left, ← mul_assoc]; norm_num)
  exact LinearMap.congr_fun this v

/-- **`[d_g, ι_e] = L^{B₀}_e`.** -/
theorem dG_iota (e : Fin 3) (v : Cochain) : dG (iota e v) + iota e (dG v) = LB0 e v := by
  have h := isOddDer_dG.anticommutator (isOddDer_iota e)
  have := h.ext (isEvenDer_colorActionOn Mode.isB0 e) (fun m => by
    simp only [LinearMap.add_apply, LinearMap.comp_apply, iota_generator, dG_generator,
      colorActionOn_generator]
    have hG1 : dG cochainOne = 0 := isOddDer_dG.map_one
    cases m with
    | c j a => simp [dGGen, Mode.isB0]
    | b j a =>
      cases j with
      | succ j => simp [dGGen, Mode.isB0]
      | zero =>
        have hb : bbConv 0 a = bbPair 0 0 a := by simp [bbConv]
        simp only [dGGen, Mode.isB0, if_true, map_smul, ← hb, iota_bbConv, smul_smul,
          colorGenerator, Mode.color, Mode.recolor, Finset.smul_sum]
        split_ifs <;> simp only [map_zero, hG1, zero_add] <;>
        · apply Finset.sum_congr rfl; intro c _
          rw [epsilon_swap_left, ← mul_assoc]; norm_num)
  exact LinearMap.congr_fun this v

theorem iota_zzConv (e : Fin 3) (j : ℕ) (a : Fin 3) : iota e (zzConv j a) = 0 := by
  simp only [zzConv, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [iota_bbPair, if_neg (by omega), if_neg (by omega), sub_zero]

/-- `[d_c, ι_e] = 0`. -/
theorem dC_iota (e : Fin 3) (v : Cochain) : dC (iota e v) + iota e (dC v) = 0 := by
  have h := isOddDer_dC.anticommutator (isOddDer_iota e)
  have hz : IsEvenDer (0 : Cochain →ₗ[ℂ] Cochain) := ⟨fun _ _ => by simp, fun _ => by simp⟩
  have := h.ext hz (fun m => by
    simp only [LinearMap.add_apply, LinearMap.comp_apply, iota_generator, dC_generator,
      LinearMap.zero_apply]
    have h1 : dC cochainOne = 0 := isOddDer_dC.map_one
    cases m with
    | c j a => simp [dCGen, iota_qGenerator]
    | b j a => split_ifs <;> simp [dCGen, h1])
  exact LinearMap.congr_fun this v

/-- `[d_Z, ι_e] = 0`. -/
theorem dZ_iota (e : Fin 3) (v : Cochain) : dZ (iota e v) + iota e (dZ v) = 0 := by
  have h := isOddDer_dZ.anticommutator (isOddDer_iota e)
  have hz : IsEvenDer (0 : Cochain →ₗ[ℂ] Cochain) := ⟨fun _ _ => by simp, fun _ => by simp⟩
  have := h.ext hz (fun m => by
    simp only [LinearMap.add_apply, LinearMap.comp_apply, iota_generator, dZ_generator,
      LinearMap.zero_apply]
    have h1 : dZ cochainOne = 0 := isOddDer_dZ.map_one
    cases m with
    | c j a => simp [dZGen]
    | b j a =>
      cases j with
      | zero => split_ifs <;> simp [dZGen, h1]
      | succ j => simp [dZGen, iota_zzConv])
  exact LinearMap.congr_fun this v

end KhanSL2
