module

public import KhanSL2.BCPVA
public import KhanSL2.PVAMap
public import Mathlib.LinearAlgebra.BilinearMap

@[expose] public section

/-! Even differential algebra derivations preserve the bracket if this holds
on the exterior generators. -/

noncomputable section

namespace KhanSL2

open LambdaBracket LambdaPolynomial

def bracketDerivationDefect (L : Module.End ℂ Cochain)
    (br : LambdaBracket Cochain) : LambdaBracket Cochain :=
  br.compr₂ (coefficientMap L) - br.comp L - br.compl₂ L

theorem bracketDerivationDefect_eq_zero (L : Module.End ℂ Cochain)
    (br : LambdaBracket Cochain) (a b : Cochain) :
    bracketDerivationDefect L br a b = 0 ↔
      coefficientMap L (br a b) = br (L a) b + br a (L b) := by
  change (coefficientMap L (br a b) - br (L a) b) - br a (L b) = 0 ↔ _
  rw [sub_sub, sub_eq_zero]

theorem bracketDerivationDefect_eq_zero_coeff (L : Module.End ℂ Cochain)
    (br : LambdaBracket Cochain) (a b : Cochain) :
    bracketDerivationDefect L br a b = 0 ↔
      ∀ n, L (br a b n) = br (L a) b n + br a (L b) n := by
  rw [bracketDerivationDefect_eq_zero, Finsupp.ext_iff]
  rfl

namespace CochainBracketDerivation

variable (L : Module.End ℂ Cochain) {br : LambdaBracket Cochain}
  (hP : IsPVA cochainData br)
  (hLmul : ∀ a b, L (wedge a b) = wedge (L a) b + wedge a (L b))
  (hLdeg : ∀ d a, a ∈ cochainPiece d → L a ∈ cochainPiece d)
  (hLT : ∀ a, L (translation a) = translation (L a))

include hP hLmul hLdeg in
theorem right_product {d e : Degree} {a b c : Cochain}
    (ha : a ∈ cochainPiece d) (hb : b ∈ cochainPiece e)
    (hab : bracketDerivationDefect L br a b = 0)
    (hac : bracketDerivationDefect L br a c = 0) :
    bracketDerivationDefect L br a (wedge b c) = 0 := by
  rw [bracketDerivationDefect_eq_zero_coeff] at hab hac ⊢
  intro n
  have hs (a b c : Cochain) {d e : Degree}
      (ha : a ∈ cochainPiece d) (hb : b ∈ cochainPiece e) :
      br a (wedge b c) n =
        wedge (br a b n) c + koszulSign d e • wedge b (br a c n) :=
    superLeibniz_coeff hP.super_leibniz ha hb c n
  rw [hs a b c ha hb]
  change L (wedge (br a b n) c + koszulSign d e • wedge b (br a c n)) = _
  rw [map_add, map_smul, hLmul, hLmul, hLmul b c,
    hs (L a) b c (hLdeg d a ha) hb]
  simp only [map_add, Finsupp.add_apply]
  rw [hs a (L b) c ha (hLdeg e b hb), hs a b (L c) ha hb, hab n, hac n]
  simp only [cochainData, wedge, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_add]
  abel

include hP hLdeg hLT in
theorem swap {d e : Degree} {a b : Cochain}
    (ha : a ∈ cochainPiece d) (hb : b ∈ cochainPiece e)
    (hab : bracketDerivationDefect L br a b = 0) :
    bracketDerivationDefect L br b a = 0 := by
  rw [bracketDerivationDefect_eq_zero] at hab ⊢
  rw [hP.super_skew e d b a hb ha, map_smul]
  change -koszulSign e d • coefficientMap L
      (minusVariableMinusTranslation translation (br a b)) = _
  rw [coefficientMap_skew L translation translation hLT, hab,
    skew_add, smul_add]
  rw [hP.super_skew e d (L b) a (hLdeg e b hb) ha,
    hP.super_skew e d b (L a) hb (hLdeg d a ha)]
  exact add_comm _ _

include hP hLmul hLdeg in
theorem right_of_generators (hLone : L cochainOne = 0)
    {d : Degree} {a : Cochain} (ha : a ∈ cochainPiece d)
    (hgen : ∀ m, bracketDerivationDefect L br a (generator m) = 0) :
    ∀ b, bracketDerivationDefect L br a b = 0 := by
  have h1 : bracketDerivationDefect L br a cochainOne = 0 := by
    rw [bracketDerivationDefect_eq_zero]
    rw [cochain_bracket_one hP.super_leibniz ha,
      cochain_bracket_one hP.super_leibniz (hLdeg d a ha), hLone]
    simp
  intro b
  induction b using cochain_induction with
  | hzero => exact (bracketDerivationDefect L br a).map_zero
  | hone => exact h1
  | hadd b c hb hc => rw [map_add, hb, hc, add_zero]
  | hsmul r b hb => rw [map_smul, hb, smul_zero]
  | hgen m b hb =>
    exact right_product L hP hLmul hLdeg ha (cochain_generator_mem m) (hgen m) hb

include hP hLmul hLdeg hLT in
theorem of_generators (hLone : L cochainOne = 0)
    (hgen : ∀ m n, bracketDerivationDefect L br (generator m) (generator n) = 0) :
    ∀ a b, bracketDerivationDefect L br a b = 0 := by
  have hG (m : Mode) (b : Cochain) :
      bracketDerivationDefect L br (generator m) b = 0 :=
    right_of_generators L hP hLmul hLdeg hLone (cochain_generator_mem m) (hgen m) b
  have hh {d : Degree} {a : Cochain} (ha : a ∈ cochainPiece d) (b : Cochain) :
      bracketDerivationDefect L br a b = 0 := by
    apply right_of_generators L hP hLmul hLdeg hLone ha _ b
    intro m
    exact swap L hP hLdeg hLT (cochain_generator_mem m) ha (hG m a)
  intro a b
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a c ha hc => simp [ha, hc]
  | single s r => exact hh (cochain_single_mem s r) b

end CochainBracketDerivation
end KhanSL2
