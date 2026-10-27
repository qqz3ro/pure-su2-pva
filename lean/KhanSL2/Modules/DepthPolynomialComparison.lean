module

public import KhanSL2.Modules.PowerSumCoordinates
public import KhanSL2.Modules.PolynomialSectors
public import KhanSL2.Depth.SourceModules

@[expose] public section

/-!
# Comparing the concrete root modules with the depth coordinate presentation

The coefficient ring in `Depth` uses elementary symmetric coordinates. Its
Vandermonde convention reverses each difference; the resulting factor is the
unit `(-1)^(s.choose 2)`. The polynomial carriers and scalar substitutions are
identified explicitly below.
-/

noncomputable section

namespace KhanSL2.Modules

open Finset MvPolynomial Injectivity

/-- The depth coordinate ring is the elementary presentation of the same `R B`. -/
abbrev depthCoefficientEquiv (B : ℕ) : Depth.RB B ≃ₐ[ℂ] R B := elementaryAlgEquiv B

theorem depthBlockSymmetric_eq (r s : ℕ) :
    Depth.symmBoth r s = blockSymmetric r s := by
  ext q
  rfl

/-- The depth presentation labels the three copies in the other product order. -/
def depthRootIndexEquiv (r s : ℕ) : Fin r ⊕ (Fin s × Fin 3) ≃ Fin (r + 3 * s) :=
  (Equiv.sumCongr (Equiv.refl (Fin r)) (Equiv.prodComm (Fin s) (Fin 3))).trans
    (rootIndexEquiv r s)

theorem weightedRootIndex_depthRootIndexEquiv (r s : ℕ)
    (a : Fin r ⊕ (Fin s × Fin 3)) :
    weightedRootIndex r s (depthRootIndexEquiv r s a) = Depth.tupleMap r s a := by
  cases a with
  | inl i => simp [depthRootIndexEquiv, rootProjection, Depth.tupleMap]
  | inr a => simp [depthRootIndexEquiv, rootProjection, Depth.tupleMap]

/-- Both maps substitute one copy of each first-block root and three of each second-block root. -/
theorem nu_depthCoefficientEquiv (r s : ℕ) (q : Depth.RB (r + 3 * s)) :
    (nu r s (depthCoefficientEquiv (r + 3 * s) q) : Polynomial r s) =
      Depth.nuStar (r + 3 * s) r s q := by
  have h : ((blockSymmetric r s).val.comp
      ((nu r s).comp (depthCoefficientEquiv (r + 3 * s)).toAlgHom)) =
      Depth.nuStar (r + 3 * s) r s := by
    ext i : 1
    change rename (weightedRootIndex r s)
      ((depthCoefficientEquiv (r + 3 * s) (X i)).val) = _
    rw [elementaryAlgEquiv_X, Depth.nuStar_X]
    change rename (weightedRootIndex r s) (esymm (Fin (r + 3 * s)) ℂ (i.val + 1)) = _
    rw [← rename_esymm (Fin r ⊕ (Fin s × Fin 3)) ℂ (i.val + 1) (depthRootIndexEquiv r s), rename_rename]
    have hfun : weightedRootIndex r s ∘ depthRootIndexEquiv r s = Depth.tupleMap r s := by
      funext a
      exact weightedRootIndex_depthRootIndexEquiv r s a
    rw [hfun]
  exact DFunLike.congr_fun h q

theorem nu_depthCoefficientEquiv_of_eq {B r s : ℕ} (h : B = r + 3 * s)
    (q : Depth.RB B) :
    (nu r s (ringCast h (depthCoefficientEquiv B q)) : Polynomial r s) =
      Depth.nuStar B r s q := by
  subst B
  simpa [ringCast] using nu_depthCoefficientEquiv r s q

private theorem orderedPair_card (n : ℕ) : Fintype.card (OrderedPair n) = n.choose 2 := by
  classical
  calc
    Fintype.card (OrderedPair n) =
        (univ.filter (fun a : Fin n × Fin n => a.1 < a.2)).card :=
      Fintype.card_of_subtype _ (by simp)
    _ = n.choose 2 := by simpa using (Fintype.card_product_filter_lt (α := Fin n))

private theorem reverse_vandermonde {A : Type*} [CommRing A]
    {n : ℕ} (v : Fin n → A) :
    (∏ i : Fin n, ∏ j ∈ Ioi i, (v i - v j)) =
      (-1) ^ (n.choose 2) * ∏ i : Fin n, ∏ j ∈ Ioi i, (v j - v i) := by
  rw [← orderedPair_prod (fun a : Fin n × Fin n => v a.1 - v a.2),
    ← orderedPair_prod (fun a : Fin n × Fin n => v a.2 - v a.1)]
  calc
    (∏ a : OrderedPair n, (v a.val.1 - v a.val.2)) =
        ∏ a : OrderedPair n, -(v a.val.2 - v a.val.1) := by
          apply prod_congr rfl
          intro a ha
          ring
    _ = _ := by rw [Finset.prod_neg, Finset.card_univ, orderedPair_card]

theorem depth_vandermondeZ (r s : ℕ) :
    Depth.vandermondeZ r s = (-1) ^ (r.choose 2) * xVandermonde r s := by
  rw [Depth.vandermondeZ, xVandermonde, Matrix.det_vandermonde]
  exact reverse_vandermonde _

theorem depth_vandermondeW (r s : ℕ) :
    Depth.vandermondeW r s = (-1) ^ (s.choose 2) * yVandermonde r s := by
  rw [Depth.vandermondeW, yVandermonde, Matrix.det_vandermonde]
  exact reverse_vandermonde _

/-- The exact unit relating the two Vandermonde orientations. -/
def depthOrientation (r s : ℕ) : Polynomial r s := (-1) ^ (s.choose 2)

@[simp] theorem depthOrientation_sq (r s : ℕ) : depthOrientation r s ^ 2 = 1 := by
  rw [depthOrientation, ← pow_mul, Nat.mul_comm (s.choose 2) 2, pow_mul]
  norm_num

theorem depthOrientation_mul_self (r s : ℕ) :
    depthOrientation r s * depthOrientation r s = 1 := by
  simpa only [pow_two] using depthOrientation_sq r s

theorem depthOrientation_mem (r s : ℕ) : depthOrientation r s ∈ blockSymmetric r s := by
  exact (blockSymmetric r s).pow_mem ((blockSymmetric r s).neg_mem (blockSymmetric r s).one_mem) _

/-- The imported discriminant and the existing one differ by the displayed unit. -/
theorem depth_Fpoly_eq (r s : ℕ) :
    Depth.Fpoly r s = depthOrientation r s * discriminantFactor r s := by
  rw [Depth.Fpoly, depth_vandermondeZ, depth_vandermondeW, discriminantFactor_eq]
  have hz : ((-1 : Polynomial r s) ^ (r.choose 2)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm (r.choose 2) 2, pow_mul]
    norm_num
  have hw : ((-1 : Polynomial r s) ^ (s.choose 2)) ^ 2 = 1 := depthOrientation_sq r s
  have hc : (∏ i : Fin r, ∏ a : Fin s, (X (Sum.inl i) - X (Sum.inr a) : Polynomial r s) ^ 2) =
      crossFactor r s ^ 2 := by simp only [crossFactor, Finset.prod_pow]
  rw [hc, mul_pow, mul_pow, hz, one_mul]
  rw [pow_succ _ 2, hw, one_mul]
  change _ = (-1) ^ (s.choose 2) * _
  ring

/-- Membership agrees for the actual polynomial, for every coefficient-ring index. -/
theorem mem_depthJ_iff (B r s : ℕ) (q : Polynomial r s) :
    (show Depth.RootsMod B r s from q) ∈ Depth.J B r s ↔ q ∈ JSubmodule r s := by
  change (∃ a : Polynomial r s, a ∈ Depth.symmBoth r s ∧ q = Depth.Fpoly r s * a) ↔ _
  rw [depthBlockSymmetric_eq, mem_JSubmodule_iff]
  constructor
  · rintro ⟨a, ha, hq⟩
    refine ⟨depthOrientation r s * a, (blockSymmetric r s).mul_mem (depthOrientation_mem r s) ha, ?_⟩
    rw [hq, depth_Fpoly_eq]
    ring
  · rintro ⟨a, ha, hq⟩
    refine ⟨depthOrientation r s * a, (blockSymmetric r s).mul_mem (depthOrientation_mem r s) ha, ?_⟩
    rw [depth_Fpoly_eq, hq]
    calc
      discriminantFactor r s * a =
          (depthOrientation r s * depthOrientation r s) * (discriminantFactor r s * a) := by
            rw [depthOrientation_mul_self, one_mul]
      _ = _ := by ring

instance elementaryRingHomInvPair (B : ℕ) :
    RingHomInvPair (elementaryAlgEquiv B).toRingHom (elementaryAlgEquiv B).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (elementaryAlgEquiv B).toRingEquiv

instance elementaryRingHomInvPairSymm (B : ℕ) :
    RingHomInvPair (elementaryAlgEquiv B).symm.toRingHom (elementaryAlgEquiv B).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (elementaryAlgEquiv B).toRingEquiv

/-- The identity on polynomials, semilinear over elementary symmetric coordinates. -/
def depthJEquiv (r s : ℕ) :
    ↥(Depth.J (r + 3 * s) r s) ≃ₛₗ[(elementaryAlgEquiv (r + 3 * s)).toRingHom] J r s where
  toFun q := ⟨q.val, (mem_depthJ_iff (r + 3 * s) r s q.val).mp q.property⟩
  invFun q := ⟨q.val, (mem_depthJ_iff (r + 3 * s) r s q.val).mpr q.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a q := by
    apply Subtype.ext
    change Depth.nuStar (r + 3 * s) r s a * (show Polynomial r s from q.val) =
      (nu r s (elementaryAlgEquiv (r + 3 * s) a) : Polynomial r s) * (show Polynomial r s from q.val)
    rw [nu_depthCoefficientEquiv]

@[simp] theorem depthJEquiv_coe (r s : ℕ) (q : ↥(Depth.J (r + 3 * s) r s)) :
    (depthJEquiv r s q).val = (show Polynomial r s from q.val) := rfl

end KhanSL2.Modules



