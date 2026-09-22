import QO7LiteralMean
import QR14GaugeReality

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 800000

open scoped ComplexConjugate BigOperators

namespace Grad.NonlinearRange

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.CompletedReality

variable {parameters : PhaseParameters}

theorem coordinateCore_conjugate {dimension : ℕ} (coordinate : Fin 2)
    (field : ACore parameters dimension) :
    cartesianCoreConjugation parameters (coordinateCore parameters coordinate field) =
      coordinateCore parameters coordinate (cartesianCoreConjugation parameters field) := by
  apply acore_ext
  intro cell point
  change cartesianPhysicalConjugation dimension
    (point.val coordinate • (field.val (-cell)).value point) =
      point.val coordinate • cartesianPhysicalConjugation dimension ((field.val (-cell)).value point)
  exact (cartesianPhysicalConjugation dimension).map_smul _ _

theorem partialCore_conjugate {dimension : ℕ} (direction : Fin 2)
    (field : ACore parameters dimension) :
    cartesianCoreConjugation parameters (partialCore parameters direction field) =
      partialCore parameters direction (cartesianCoreConjugation parameters field) := by
  apply acore_ext
  intro cell point
  change cartesianPhysicalConjugation dimension
    (closedDerivative (field.val (-cell)) 1 (fun _ => direction) point) =
      closedDerivative (closedJetConjugate (field.val (-cell))) 1 (fun _ => direction) point
  rw [closedJetConjugate_derivative]
  rfl

theorem eulerCore_conjugate {dimension : ℕ} (field : ACore parameters dimension) :
    cartesianCoreConjugation parameters (eulerCore parameters field) =
      eulerCore parameters (cartesianCoreConjugation parameters field) := by
  change cartesianCoreConjugation parameters
    (coordinateCore parameters 0 (partialCore parameters 0 field) +
      coordinateCore parameters 1 (partialCore parameters 1 field)) = _
  rw [map_add, coordinateCore_conjugate, coordinateCore_conjugate,
    partialCore_conjugate, partialCore_conjugate]
  rfl

theorem rotationCore_conjugate {dimension : ℕ} (field : ACore parameters dimension) :
    cartesianCoreConjugation parameters (rotationCore parameters field) =
      rotationCore parameters (cartesianCoreConjugation parameters field) := by
  change cartesianCoreConjugation parameters
    (coordinateCore parameters 0 (partialCore parameters 1 field) -
      coordinateCore parameters 1 (partialCore parameters 0 field)) = _
  rw [map_sub, coordinateCore_conjugate, coordinateCore_conjugate,
    partialCore_conjugate, partialCore_conjugate]
  rfl

theorem timeDerivativeCore_conjugate {dimension : ℕ} (field : ACore parameters dimension) :
    cartesianCoreConjugation parameters (timeDerivativeCore parameters field) =
      timeDerivativeCore parameters (cartesianCoreConjugation parameters field) := by
  apply Subtype.ext
  funext cell
  change closedJetConjugate ((((-cell : ℤ) : ℂ) * Complex.I) • field.val (-cell)) =
    ((cell : ℂ) * Complex.I) • closedJetConjugate (field.val (-cell))
  rw [closedJetConjugate_complex_smul]
  simp

theorem partialPlusCore_conjugate {dimension : ℕ} (field : ACore parameters dimension) :
    cartesianCoreConjugation parameters (partialPlusCore parameters field) =
      partialMinusCore parameters (cartesianCoreConjugation parameters field) := by
  change cartesianCoreConjugation parameters
    (partialCore parameters 0 field + Complex.I • partialCore parameters 1 field) = _
  rw [map_add, coreConjugation_complex_smul, partialCore_conjugate, partialCore_conjugate]
  change partialCore parameters 0 (cartesianCoreConjugation parameters field) +
    conj Complex.I • partialCore parameters 1 (cartesianCoreConjugation parameters field) =
    partialCore parameters 0 (cartesianCoreConjugation parameters field) -
    Complex.I • partialCore parameters 1 (cartesianCoreConjugation parameters field)
  rw [Complex.conj_I]
  module

theorem partialMinusCore_conjugate {dimension : ℕ} (field : ACore parameters dimension) :
    cartesianCoreConjugation parameters (partialMinusCore parameters field) =
      partialPlusCore parameters (cartesianCoreConjugation parameters field) := by
  have equality := congrArg (cartesianCoreConjugation parameters)
    (partialPlusCore_conjugate (cartesianCoreConjugation parameters field))
  rw [cartesianCoreConjugation_involutive, cartesianCoreConjugation_involutive] at equality
  exact equality.symm

theorem zMulCore_conjugate {dimension : ℕ} (field : ACore parameters dimension) :
    cartesianCoreConjugation parameters (zMulCore parameters field) =
      starZMulCore parameters (cartesianCoreConjugation parameters field) := by
  change cartesianCoreConjugation parameters
    (coordinateCore parameters 0 field + Complex.I • coordinateCore parameters 1 field) = _
  rw [map_add, coreConjugation_complex_smul, coordinateCore_conjugate, coordinateCore_conjugate]
  change coordinateCore parameters 0 (cartesianCoreConjugation parameters field) +
    conj Complex.I • coordinateCore parameters 1 (cartesianCoreConjugation parameters field) =
    coordinateCore parameters 0 (cartesianCoreConjugation parameters field) -
    Complex.I • coordinateCore parameters 1 (cartesianCoreConjugation parameters field)
  rw [Complex.conj_I]
  module

theorem starZMulCore_conjugate {dimension : ℕ} (field : ACore parameters dimension) :
    cartesianCoreConjugation parameters (starZMulCore parameters field) =
      zMulCore parameters (cartesianCoreConjugation parameters field) := by
  have equality := congrArg (cartesianCoreConjugation parameters)
    (zMulCore_conjugate (cartesianCoreConjugation parameters field))
  rw [cartesianCoreConjugation_involutive, cartesianCoreConjugation_involutive] at equality
  exact equality.symm

theorem removeAngularCore_conjugate {dimension : ℕ} (field : ACore parameters dimension) :
    cartesianCoreConjugation parameters (removeAngularCore parameters field) =
      removeAngularCore parameters (cartesianCoreConjugation parameters field) := by
  change cartesianCoreConjugation parameters (field - angularCore parameters 0 field) = _
  rw [map_sub, angularCore_conjugate, neg_zero]
  rfl

end Grad.NonlinearRange
