module

import all KhanSL2.Basic
import all KhanSL2.ExteriorAlgebra
import all KhanSL2.ExteriorSigns
import all KhanSL2.ExteriorParity
import all KhanSL2.ExteriorRing
import all KhanSL2.ExteriorSupercomm
import all KhanSL2.Injectivity.ExteriorSubstitution
import all KhanSL2.BGG.ExteriorModel
import all KhanSL2.CE
import all KhanSL2.Cocycles
import all KhanSL2.CEDerivationBasics
import all KhanSL2.BasisGrading
import all KhanSL2.CochainGrading
import all KhanSL2.CEDegrees
import all KhanSL2.CEExterior
import all KhanSL2.PVA
import all KhanSL2.CochainSupercomm
import all KhanSL2.ExteriorContraction
import all KhanSL2.ExteriorDerivation
import all KhanSL2.CELeibniz
import all KhanSL2.CESeries
import all KhanSL2.CESquareZero
import all KhanSL2.BGG.PositiveCE
import all KhanSL2.Injectivity.FinitePairing
import all KhanSL2.Injectivity.FiniteSupport
import all KhanSL2.BGG.PositiveBoundary
import all KhanSL2.BGG.PositiveBoundaryAdjoint
import all KhanSL2.BGG.PolynomialKoszul
import all KhanSL2.Macdonald.Basic
import all KhanSL2.Macdonald.Grading
import all KhanSL2.Macdonald.FinitePieces
import all KhanSL2.Macdonald.Generators
import all KhanSL2.Macdonald.GeneratorDegrees
import all KhanSL2.Macdonald.CoefficientShift
import all KhanSL2.Macdonald.GeneratorShift
import all KhanSL2.Macdonald.Milestone

public import Lean.Elab.Command
public import Lean.Util.CollectAxioms

/-!
Audit of the first Macdonald milestone. Every project module in its closure
is imported with all proof bodies, including private helpers. The audit checks
all safe project declarations against the three standard Lean axioms and
rejects unsafe declarations in the new Macdonald modules.

This audit establishes no CE cohomology calculation. The milestone asserts
only finite-dimensional graded pieces and identities for explicit elements
and a coefficient-lowering operator in the concrete mixed algebra.
-/

open Lean Elab Command

elab "#audit_macdonald_generators" : command => do
  let env ← getEnv
  let isProjectModule := fun (name : Name) => (`KhanSL2).isPrefixOf name
  for imported in env.header.modules do
    if isProjectModule imported.module && !imported.importAll then
      throwError "Missing project proof bodies in {imported.module}"
  for n in #[`KhanSL2.Macdonald.milestoneGenerators,
      `KhanSL2.Macdonald.sigma_commute, `KhanSL2.Macdonald.psi_anticomm,
      `KhanSL2.Macdonald.sigma_mem_piece, `KhanSL2.Macdonald.psi_mem_piece,
      `KhanSL2.Macdonald.mul_mem_piece,
      `KhanSL2.Macdonald.piece_eq_bot_of_weight_lt_degree,
      `KhanSL2.Macdonald.S_mem_piece, `KhanSL2.Macdonald.E_mem_piece,
      `KhanSL2.Macdonald.coefficientShift_mul,
      `KhanSL2.Macdonald.coefficientShift_sigma, `KhanSL2.Macdonald.coefficientShift_psi,
      `KhanSL2.Macdonald.coefficientShift_S, `KhanSL2.Macdonald.coefficientShift_E] do
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Expected proved theorem {n}"
  let names := env.constants.toList.filterMap fun (n, info) =>
    let included := match env.getModuleIdxFor? n with
      | some idx => isProjectModule env.header.moduleNames[idx.toNat]!
      | none => false
    if included && !info.isUnsafe then some n else none
  for (n, info) in env.constants.toList do
    let fromMacdonald := match env.getModuleIdxFor? n with
      | some idx => (`KhanSL2.Macdonald).isPrefixOf env.header.moduleNames[idx.toNat]!
      | none => false
    if fromMacdonald && info.isUnsafe then
      throwError "Unsafe declaration in Macdonald development: {n}"
  for required in #[`KhanSL2.Macdonald.basis, `KhanSL2.Macdonald.sigma,
      `KhanSL2.Macdonald.psi, `KhanSL2.Macdonald.piece,
      `KhanSL2.Macdonald.S, `KhanSL2.Macdonald.E,
      `KhanSL2.Macdonald.polynomialShift, `KhanSL2.Macdonald.coefficientShift,
      `KhanSL2.Macdonald.milestoneGenerators] do
    unless names.contains required do
      throwError "Required declaration is missing from the proof audit: {required}"
  for n in names do
    for ax in (← collectAxioms n) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Forbidden axiom in {n}: {ax}"
  logInfo m!"PASS: {names.length} safe declarations in the Macdonald milestone's project closure; no sorryAx or additional axioms."
  logInfo "The proved milestone concerns the concrete mixed algebra and generators; no CE cohomology theorem is asserted."

noncomputable section
open scoped BigOperators TensorProduct
open KhanSL2.Macdonald

-- Fix the concrete algebra and the two explicit candidate generators.
example : W = Poly ⊗[ℂ] Exterior := rfl
example (n : ℕ) : S n =
    ∑ a : Fin 3, ∑ i ∈ Finset.range (n + 1), sigma a i * sigma a (n - i) := rfl
example (n : ℕ) : E n =
    ∑ a : Fin 3, ∑ i ∈ Finset.range n,
      ((i + 1 : ℕ) : ℂ) • (sigma a (n - 1 - i) * psi a i) := rfl

-- Physical mode and fixed-degree checks include the even zero mode.
#check (sigma_mem_piece : ∀ (a : Fin 3) (n : ℕ), sigma a n ∈ piece n 1 0)
#check (psi_mem_piece : ∀ (a : Fin 3) (i : ℕ), psi a i ∈ piece (i + 1) 0 1)
example (w s k : ℕ) : FiniteDimensional ℂ (piece w s k) := inferInstance
example (w s : ℕ) : FiniteDimensional ℂ (weightDegreePiece w s) := inferInstance
example (w s k : ℕ) (h : w < k) : piece w s k = ⊥ :=
  piece_eq_bot_of_weight_lt_degree h
#check (S_mem_piece : ∀ n : ℕ, S n ∈ piece n 2 0)
#check (E_mem_piece : ∀ n : ℕ, E n ∈ piece n 1 1)

-- W is not commutative, so audit the actual Leibniz identity of the linear operator.
#check (coefficientShift : ℕ → Module.End ℂ W)
#check (coefficientShift_mul : ∀ (m : ℕ) (u v : W),
  coefficientShift m (u * v) = coefficientShift m u * v + u * coefficientShift m v)
#check (coefficientShift_S : ∀ m n : ℕ,
  coefficientShift m (S n) = if m ≤ n then (2 : ℂ) • S (n - m) else 0)
#check (coefficientShift_E : ∀ m n : ℕ,
  coefficientShift m (E n) = E (n - m))
example (n : ℕ) : coefficientShift 0 (S n) = (2 : ℂ) • S n := by
  simp [coefficientShift_S]
example (n : ℕ) : coefficientShift 0 (E n) = E n := by
  simp [coefficientShift_E]
example (n : ℕ) : coefficientShift n (S n) = (2 : ℂ) • S 0 :=
  coefficientShift_S_self n
example (n : ℕ) : coefficientShift n (E n) = 0 := coefficientShift_E_self n

#check milestoneGenerators
#audit_macdonald_generators
#print axioms milestoneGenerators
#print axioms coefficientShift_S
#print axioms coefficientShift_E
