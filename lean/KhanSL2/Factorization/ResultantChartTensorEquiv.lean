module

public import KhanSL2.Factorization.ResultantChartTensorEvaluation

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial TensorProduct
namespace KhanSL2.Factorization.ChartBridge

section UniversalMaps
variable {r s : ℕ} {A : Type*} [CommRing A] [Algebra (Depth.RB (r+s)) A]

theorem universal_hom_ext (f g : Universal (r+s) r s rfl →ₐ[Depth.RB (r+s)] A)
    (h₁ : (universalFirst r s).val.map f.toRingHom = (universalFirst r s).val.map g.toRingHom)
    (h₂ : (universalSecond r s).val.map f.toRingHom = (universalSecond r s).val.map g.toRingHom) :
    f = g := by
  apply (Polynomial.UniversalCoprimeFactorizationRing.homEquiv A r s rfl
    (universalPolynomial (r+s))).injective
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · simpa only [Polynomial.UniversalCoprimeFactorizationRing.homEquiv,
      Polynomial.UniversalFactorizationRing.homEquiv,Equiv.coe_fn_mk,
      universalFirst,Polynomial.UniversalCoprimeFactorizationRing.factor₁,
      MonicDegreeEq.map_coe,Polynomial.map_map,AlgHom.comp_toRingHom,
      IsScalarTower.coe_toAlgHom,AlgHom.toRingHom_eq_coe] using h₁
  · simpa only [Polynomial.UniversalCoprimeFactorizationRing.homEquiv,
      Polynomial.UniversalFactorizationRing.homEquiv,Equiv.coe_fn_mk,
      universalSecond,Polynomial.UniversalCoprimeFactorizationRing.factor₂,
      MonicDegreeEq.map_coe,Polynomial.map_map,AlgHom.comp_toRingHom,
      IsScalarTower.coe_toAlgHom,AlgHom.toRingHom_eq_coe] using h₂

end UniversalMaps

theorem universalToProductChart_first (r s : ℕ) :
    (universalFirst r s).val.map (universalToProductChart r s).toRingHom =
      (firstOnProductChart r s).val := by
  have hs : (Polynomial.UniversalCoprimeFactorizationRing.homEquiv (ProductChart r s) r s rfl
      (universalPolynomial (r+s))) (universalToProductChart r s) =
      ⟨⟨firstOnProductChart r s,secondOnProductChart r s⟩,
        productChart_factorization r s,productChart_isCoprime r s⟩ :=
    Equiv.apply_symm_apply _ _
  have h := congrArg (fun t => t.val.1.val) hs
  simpa only [Polynomial.UniversalCoprimeFactorizationRing.homEquiv,
    Polynomial.UniversalFactorizationRing.homEquiv,Equiv.coe_fn_mk,
    universalFirst,Polynomial.UniversalCoprimeFactorizationRing.factor₁,
    MonicDegreeEq.map_coe,Polynomial.map_map,AlgHom.comp_toRingHom,
    IsScalarTower.coe_toAlgHom,AlgHom.toRingHom_eq_coe] using h

theorem universalToProductChart_second (r s : ℕ) :
    (universalSecond r s).val.map (universalToProductChart r s).toRingHom =
      (secondOnProductChart r s).val := by
  have hs : (Polynomial.UniversalCoprimeFactorizationRing.homEquiv (ProductChart r s) r s rfl
      (universalPolynomial (r+s))) (universalToProductChart r s) =
      ⟨⟨firstOnProductChart r s,secondOnProductChart r s⟩,
        productChart_factorization r s,productChart_isCoprime r s⟩ :=
    Equiv.apply_symm_apply _ _
  have h := congrArg (fun t => t.val.2.val) hs
  simpa only [Polynomial.UniversalCoprimeFactorizationRing.homEquiv,
    Polynomial.UniversalFactorizationRing.homEquiv,Equiv.coe_fn_mk,
    universalSecond,Polynomial.UniversalCoprimeFactorizationRing.factor₂,
    MonicDegreeEq.map_coe,Polynomial.map_map,AlgHom.comp_toRingHom,
    IsScalarTower.coe_toAlgHom,AlgHom.toRingHom_eq_coe] using h

theorem productChartToUniversal_first (r s : ℕ) :
    (firstOnProductChart r s).val.map (productChartToUniversal r s).toRingHom =
      (universalFirst r s).val := by
  change ((firstPolynomial r s).val.map _).map _ = _
  rw [Polynomial.map_map]
  have hc : (productChartToUniversal r s).toRingHom.comp
      (algebraMap (ProductCoefficients r s) (ProductChart r s)) =
        (productToUniversal r s).toRingHom :=
    RingHom.ext (productChartToUniversal_algebraMap r s)
  rw [hc]
  exact productEvaluation_first (universalFirst r s) (universalSecond r s)

theorem productChartToUniversal_second (r s : ℕ) :
    (secondOnProductChart r s).val.map (productChartToUniversal r s).toRingHom =
      (universalSecond r s).val := by
  change ((secondPolynomial r s).val.map _).map _ = _
  rw [Polynomial.map_map]
  have hc : (productChartToUniversal r s).toRingHom.comp
      (algebraMap (ProductCoefficients r s) (ProductChart r s)) =
        (productToUniversal r s).toRingHom :=
    RingHom.ext (productChartToUniversal_algebraMap r s)
  rw [hc]
  exact productEvaluation_second (universalFirst r s) (universalSecond r s)

theorem productChartToUniversal_comp (r s : ℕ) :
    (productChartToUniversal r s).comp (universalToProductChart r s) =
      AlgHom.id (Depth.RB (r+s)) (Universal (r+s) r s rfl) := by
  apply universal_hom_ext
  · change (universalFirst r s).val.map
      ((productChartToUniversal r s).toRingHom.comp (universalToProductChart r s).toRingHom) =
      (universalFirst r s).val.map (RingHom.id _)
    rw [← Polynomial.map_map,universalToProductChart_first,productChartToUniversal_first,
      Polynomial.map_id]
  · change (universalSecond r s).val.map
      ((productChartToUniversal r s).toRingHom.comp (universalToProductChart r s).toRingHom) =
      (universalSecond r s).val.map (RingHom.id _)
    rw [← Polynomial.map_map,universalToProductChart_second,productChartToUniversal_second,
      Polynomial.map_id]

end KhanSL2.Factorization.ChartBridge
