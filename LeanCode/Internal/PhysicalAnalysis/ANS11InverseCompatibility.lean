import ANS10ActualAngularConsumer

noncomputable section
set_option maxHeartbeats 1600000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.ActualAngularInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange Grad.NonlinearDivision
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra

theorem shiftInverseJet_valueMap {firstDimension secondDimension : ℕ}
    (mapping : ComplexEuclidean firstDimension →L[ℂ] ComplexEuclidean secondDimension)
    (shift : ℤ) (field : ClosedJet firstDimension) :
    shiftInverseJet shift (valueMapJet mapping field) = valueMapJet mapping (shiftInverseJet shift field) := by
  apply closedJet_angular_ext
  intro mode
  rw [shiftInverseJet_coefficient, angularClosedJet_valueMap, angularClosedJet_valueMap,
    shiftInverseJet_coefficient]
  by_cases resonant : mode = -shift
  · simp only [if_pos resonant, valueMapJet_map_zero]
  · simp only [if_neg resonant]
    exact (map_smul (valueMapJetLinear firstDimension secondDimension mapping) _ _).symm

theorem shiftInverseJet_angular {dimension : ℕ} (shift mode : ℤ) (field : ClosedJet dimension) :
    shiftInverseJet shift (angularClosedJet mode field) = angularClosedJet mode (shiftInverseJet shift field) := by
  apply closedJet_angular_ext
  intro other
  rw [shiftInverseJet_coefficient, angularClosedJet_projection, angularClosedJet_projection]
  by_cases same : other = mode
  · subst other
    simpa using (shiftInverseJet_coefficient shift mode field).symm
  · simp only [if_neg same]
    by_cases resonant : other = -shift <;> simp [resonant]

theorem shiftInverseJet_firstJet {dimension : ℕ} (shift : ℤ) (field : ClosedJet dimension)
    (flat : ClosedFirstJetZero field) : ClosedFirstJetZero (shiftInverseJet shift field) := by
  constructor
  · have zero := shiftInverse_preserves_zero_derivatives (order := 0) shift field
      (fun word => by
        rw [Subsingleton.elim word emptyCartesianWord, closedDerivative_zero_order]
        exact flat.1) emptyCartesianWord
    simpa only [closedDerivative_zero_order, closedOrigin] using! zero
  · intro direction
    apply shiftInverse_preserves_zero_derivatives (order := 1) shift field
    intro word
    have constant : word = fun _ => word 0 := by funext position; fin_cases position; rfl
    rw [constant]
    exact flat.2 (word 0)

variable {L sigma gamma ell : ℝ}

theorem apShiftInverse_valueMap (admissible : Admissible L sigma gamma ell)
    {firstDimension secondDimension : ℕ}
    (mapping : ComplexEuclidean firstDimension →L[ℂ] ComplexEuclidean secondDimension)
    (shift : ℤ) (field : APSmooth L sigma gamma ell firstDimension) :
    apShiftInverse admissible shift (apSmoothValueMap L sigma gamma ell mapping field) =
      apSmoothValueMap L sigma gamma ell mapping (apShiftInverse admissible shift field) := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apShiftInverse_jet admissible shift _ cell).trans
    ((congrArg (shiftInverseJet shift) (apSmoothValueMap_jet admissible mapping field cell)).trans
      ((shiftInverseJet_valueMap mapping shift _).trans
        ((congrArg (valueMapJet mapping) (apShiftInverse_jet admissible shift field cell).symm).trans
          (apSmoothValueMap_jet admissible mapping _ cell).symm)))

theorem apShiftInverse_firstJet (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (shift : ℤ) (field : APSmooth L sigma gamma ell dimension)
    (flat : APSmoothAxisFirstJetZero admissible field) :
    APSmoothAxisFirstJetZero admissible (apShiftInverse admissible shift field) := by
  apply apSmoothAxisFirstJetZero_of_closed admissible
  intro cell
  exact (congrArg ClosedFirstJetZero (apShiftInverse_jet admissible shift field cell)).mpr
    (shiftInverseJet_firstJet shift _ (apSmoothAxisFirstJetZero_closed admissible field flat cell))

/-- The AN11/AN12 inverses are the shifts 1,-1,0 of this same original-width
complex linear construction, with actual R graph estimates and preserved jets. -/
theorem actualPartialSpinInverses (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (shift : ℤ) (source : APSmooth L sigma gamma ell dimension)
    (nonresonant : APNonresonant admissible shift source) :
    APNonresonant admissible shift (apShiftInverseLinear admissible dimension shift source) ∧
    apShiftedRotation admissible dimension shift (apShiftInverseLinear admissible dimension shift source) = source ∧
    (∀ grade, ‖apSmoothGrade L sigma gamma ell dimension grade
      (apShiftInverseLinear admissible dimension shift source)‖ ≤
        angularInverseConstant grade * ‖apSmoothGrade L sigma gamma ell dimension grade source‖) ∧
    (APSmoothAxisFirstJetZero admissible source →
      APSmoothAxisFirstJetZero admissible (apShiftInverseLinear admissible dimension shift source)) :=
  ⟨apShiftInverse_nonresonant admissible shift source, apShiftInverse_solves admissible shift source nonresonant,
    fun grade => apShiftInverse_bound admissible shift grade source, apShiftInverse_firstJet admissible shift source⟩

end Grad.ActualAngularInverse
