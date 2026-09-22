import QR14GaugeReality

noncomputable section

open scoped ComplexConjugate

namespace Grad.CompletedReality

open MeasureTheory
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.BoundaryTrace Grad.BoundaryLift Grad.Cor18

theorem fourierCoeff_conjugate (field : CellCircle → ℂ) (mode : ℤ) :
    fourierCoeff (fun angle => conj (field angle)) mode = conj (fourierCoeff field (-mode)) := by
  unfold fourierCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with angle
  simp only [neg_neg, smul_eq_mul, map_mul, fourier_neg]

theorem rowField_conjugate (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore parameters 3) :
    cartesianCoreConjugation parameters (rowField parameters parameter inside field) =
      rowField parameters parameter inside (cartesianCoreConjugation parameters field) := by
  change cartesianCoreConjugation parameters
    (seedInverseCore parameters parameter inside (planarPartCore parameters field)) = _
  rw [seedInverseCore_conjugate, planarPartCore_conjugate]
  rfl

theorem rowFunction_conjugate (parameters : PhaseParameters) (field : ACore parameters 2)
    (cell : ℤ) :
    rowFunction parameters (cartesianCoreConjugation parameters field) cell =
      fun angle => conj (rowFunction parameters field (-cell) angle) := by
  funext angle
  simp only [rowFunction, cartesianCoreConjugation_apply, closedJetConjugate_value_apply,
    map_add, map_mul, Complex.conj_ofReal]

/-- The actual physical boundary row has joint angular/cell conjugate reversal. -/
theorem physicalRow_conjugate_coefficient (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore parameters 3) (angular cell : ℤ) :
    (physicalRow parameters parameter inside (cartesianCoreConjugation parameters field)).1 (angular, cell) =
      cartesianPhysicalConjugation 1
        ((physicalRow parameters parameter inside field).1 (-angular, -cell)) := by
  change physicalRowFamily parameters parameter inside (cartesianCoreConjugation parameters field)
    (angular, cell) = cartesianPhysicalConjugation 1
      (physicalRowFamily parameters parameter inside field (-angular, -cell))
  simp only [physicalRowFamily, abs_neg, ← rowField_conjugate, rowFunction_conjugate,
    fourierCoeff_conjugate]
  by_cases low : |angular| ≤ 2
  · simp only [if_pos low, map_zero]
  · simp only [if_neg low]
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate
    simp [cartesianPhysicalConjugation_apply]

/-- The actual collar lift respects the joint reversed coefficient relation.
Both inputs are genuine all-grade boundary cores, not arbitrary weak data. -/
theorem boundaryLift_conjugate_of_coefficients {dimension : ℕ} (parameters : PhaseParameters)
    (first second : BoundaryCore parameters dimension)
    (coefficients : ∀ angular cell, second.1 (angular, cell) =
      cartesianPhysicalConjugation dimension (first.1 (-angular, -cell))) :
    cartesianCoreConjugation parameters (boundaryLift parameters first) =
      boundaryLift parameters second := by
  apply Subtype.ext
  funext cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change cartesianPhysicalConjugation dimension
    (((boundaryLift parameters first).1 (-cell)).value point) = _
  have original := boundaryLift_angular_value_hasSum parameters first (-cell) point
  have mapped : HasSum (fun angular : ℤ => cartesianPhysicalConjugation dimension
      (boundaryKernel (angular, -cell) point.val • first.1 (angular, -cell)))
      (cartesianPhysicalConjugation dimension
        (((boundaryLift parameters first).1 (-cell)).value point)) :=
    (cartesianPhysicalConjugation dimension).toContinuousLinearEquiv.toContinuousLinearMap.hasSum original
  have reindexed := (Equiv.neg ℤ).hasSum_iff.mpr mapped
  have sameTerms : HasSum (fun angular : ℤ => boundaryKernel (angular, cell) point.val •
      second.1 (angular, cell))
      (cartesianPhysicalConjugation dimension
        (((boundaryLift parameters first).1 (-cell)).value point)) := by
    apply reindexed.congr_fun
    intro angular
    change boundaryKernel (angular, cell) point.val • second.1 (angular, cell) =
      cartesianPhysicalConjugation dimension
        (boundaryKernel (-angular, -cell) point.val • first.1 (-angular, -cell))
    rw [physicalConjugation_complex_smul, boundaryKernel_conj, neg_neg,
      boundaryKernel_neg_snd, coefficients]
  exact sameTerms.unique (boundaryLift_angular_value_hasSum parameters second cell point)

end Grad.CompletedReality
