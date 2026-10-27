module

public import KhanSL2.Collision.Assembly

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
namespace KhanSL2.Factorization.ChartBridge

/-- The actual universal elementary-coordinate polynomial, with its degree bundled. -/
def universalPolynomial (B : ℕ) : MonicDegreeEq (Depth.RB B) B :=
  MonicDegreeEq.mk (Collision.univPoly B) (Collision.univPoly_monic B)
    (Collision.natDegree_univPoly B)

/-- The universal coprime factor chart for the original coefficient polynomial. -/
abbrev Universal (B r s : ℕ) (hsum : r+s=B) :=
  Polynomial.UniversalCoprimeFactorizationRing r s hsum.symm (universalPolynomial B)

variable {B r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB B) A]

/-- The factorization specified by a chart determines its actual map from the
universal coprime chart. No choice of roots or reducedness is required. -/
def specialization (hsum : r+s=B) (c : Collision.ChartData B r s A) :
    Universal B r s hsum →ₐ[Depth.RB B] A :=
  (Polynomial.UniversalCoprimeFactorizationRing.homEquiv A r s hsum.symm
    (universalPolynomial B)).symm
      ⟨⟨MonicDegreeEq.mk c.f₁ c.monic₁ c.degree₁,
        MonicDegreeEq.mk c.f₂ c.monic₂ c.degree₂⟩,c.factor.symm,c.coprime⟩

/-- Scalar extension along the specified universal-chart map. -/
abbrev specializationAlgebra (hsum : r+s=B) (c : Collision.ChartData B r s A) :
    Algebra (Universal B r s hsum) A := (specialization hsum c).toRingHom.toAlgebra

theorem specialization_tower (hsum : r+s=B) (c : Collision.ChartData B r s A) :
    let := specializationAlgebra hsum c
    IsScalarTower (Depth.RB B) (Universal B r s hsum) A := by
  let := specializationAlgebra hsum c
  exact IsScalarTower.of_algebraMap_eq fun a => ((specialization hsum c).commutes a).symm

/-- An etale chart remains etale over the universal coprime chart. This is the
cancellation step needed to extend a universal-chart calculation to KFactor's
quantifier over all etale charts. -/
theorem specialization_etale (hsum : r+s=B) (c : Collision.ChartData B r s A)
    [Algebra.Etale (Depth.RB B) A] :
    let := specializationAlgebra hsum c
    Algebra.Etale (Universal B r s hsum) A := by
  let := specializationAlgebra hsum c
  let := specialization_tower hsum c
  exact Algebra.Etale.of_restrictScalars (Depth.RB B) (Universal B r s hsum) A

/-- In particular scalar extension from the universal coprime chart is flat. -/
theorem specialization_flat (hsum : r+s=B) (c : Collision.ChartData B r s A)
    [Algebra.Etale (Depth.RB B) A] :
    let := specializationAlgebra hsum c
    Module.Flat (Universal B r s hsum) A := by
  let := specializationAlgebra hsum c
  let := specialization_etale hsum c
  infer_instance

/-- The universal property records exactly the two supplied factors. -/
theorem specialization_spec (hsum : r+s=B) (c : Collision.ChartData B r s A) :
    Polynomial.UniversalCoprimeFactorizationRing.homEquiv A r s hsum.symm
        (universalPolynomial B) (specialization hsum c) =
      ⟨⟨MonicDegreeEq.mk c.f₁ c.monic₁ c.degree₁,
        MonicDegreeEq.mk c.f₂ c.monic₂ c.degree₂⟩,c.factor.symm,c.coprime⟩ :=
  Equiv.apply_symm_apply _ _

/-- Specialization carries the first universal factor to the supplied first factor. -/
theorem specialization_factor₁ (hsum : r+s=B) (c : Collision.ChartData B r s A) :
    ((Polynomial.UniversalCoprimeFactorizationRing.factor₁ r s hsum.symm
      (universalPolynomial B)).val).map (specialization hsum c).toRingHom = c.f₁ := by
  have h := congrArg (fun t => t.val.1.val) (specialization_spec hsum c)
  simpa only [Polynomial.UniversalCoprimeFactorizationRing.homEquiv,
    Polynomial.UniversalFactorizationRing.homEquiv,
    Polynomial.UniversalCoprimeFactorizationRing.factor₁,
    Polynomial.MonicDegreeEq.map_coe, Polynomial.MonicDegreeEq.mk_coe,
    Polynomial.map_map, AlgHom.comp_toRingHom, IsScalarTower.coe_toAlgHom,
    Equiv.coe_fn_mk, AlgHom.toRingHom_eq_coe] using h

/-- Specialization carries the second universal factor to the supplied second factor. -/
theorem specialization_factor₂ (hsum : r+s=B) (c : Collision.ChartData B r s A) :
    ((Polynomial.UniversalCoprimeFactorizationRing.factor₂ r s hsum.symm
      (universalPolynomial B)).val).map (specialization hsum c).toRingHom = c.f₂ := by
  have h := congrArg (fun t => t.val.2.val) (specialization_spec hsum c)
  simpa only [Polynomial.UniversalCoprimeFactorizationRing.homEquiv,
    Polynomial.UniversalFactorizationRing.homEquiv,
    Polynomial.UniversalCoprimeFactorizationRing.factor₂,
    Polynomial.MonicDegreeEq.map_coe, Polynomial.MonicDegreeEq.mk_coe,
    Polynomial.map_map, AlgHom.comp_toRingHom, IsScalarTower.coe_toAlgHom,
    Equiv.coe_fn_mk, AlgHom.toRingHom_eq_coe] using h
end KhanSL2.Factorization.ChartBridge
