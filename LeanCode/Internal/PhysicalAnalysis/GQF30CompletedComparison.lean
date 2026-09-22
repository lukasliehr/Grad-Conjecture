import GQF29CompletedRange

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)

/-- Actual four-row common-domain realization on the specified closures.
Every record field is constructed, with no inverse or PDE solvability premise. -/
def actualCompletedForwardComparison (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation) (grade : ℕ) (large : 3 ≤ grade) :
    CompletedForwardComparison admissible data coherent smooth grade large where
  circle := completedCircularRows admissible grade (circularCompensatedCore admissible)
  current := completedCurrentRows admissible data coherent grade
    (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent)
  error := completedError admissible data coherent grade
  circleCore := completedCircularRows_core admissible grade (circularCompensatedCore admissible)
  currentCore := completedCurrentRows_core admissible data coherent grade
    (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent)
  errorCore := completedError_core admissible data coherent grade
  circleRange := completedCircularRows_range admissible grade _ inf_le_left
  currentRange := completedCurrentRows_range admissible data coherent grade _ inf_le_left
  difference := completedRows_difference admissible data coherent smooth grade large

theorem completedRows_difference_factorization (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation) (grade : ℕ) (large : 3 ≤ grade) :
    (completedCurrentRows admissible data coherent grade
      (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent)).comp
        (completedTransfer smooth grade large) -
      completedCircularRows admissible grade (circularCompensatedCore admissible) =
      ((completedError admissible data coherent grade).comp
        (completedReconstruct admissible grade
          (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent))).comp
            (completedTransfer smooth grade large) := by
  apply ContinuousLinearMap.ext
  intro field
  exact (completedRows_difference admissible data coherent smooth grade large field).trans
    (congrArg (completedError admissible data coherent grade)
      (completedReconstruct_transfer admissible smooth grade large field).symm)

theorem actualCompletedForwardComparison_circle_bound (data : LedgerData L sigma gamma ell)
    (coherent : LedgerCoherent data) (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation)
    (grade : ℕ) (large : 3 ≤ grade) :
    ‖(actualCompletedForwardComparison admissible data coherent smooth grade large).circle‖ ≤
      circularForwardConstant L sigma gamma grade :=
  completedCircularRows_bound admissible grade (circularCompensatedCore admissible)

theorem actualCompletedForwardComparison_difference_bound (data : LedgerData L sigma gamma ell)
    (coherent : LedgerCoherent data) (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation)
    (grade : ℕ) (large : 3 ≤ grade) :
    ‖(actualCompletedForwardComparison admissible data coherent smooth grade large).current.comp
      (completedTransfer smooth grade large) -
      (actualCompletedForwardComparison admissible data coherent smooth grade large).circle‖ ≤
      errorForwardConstant L sigma gamma grade * errorCoefficientSize data (grade + 1) *
        reconstructionBoundConstant L gamma grade * completedTransferConstant data.gaugeDeviation grade := by
  have bound := ContinuousLinearMap.opNorm_comp_le
    ((completedError admissible data coherent grade).comp
      (completedReconstruct admissible grade
        (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent))) (completedTransfer smooth grade large)
  have product := (ContinuousLinearMap.opNorm_comp_le (completedError admissible data coherent grade)
    (completedReconstruct admissible grade
      (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent))).trans
    (mul_le_mul (completedError_bound admissible data coherent grade)
      (completedReconstruct_bound admissible grade _)
      (ContinuousLinearMap.opNorm_nonneg (completedReconstruct admissible grade
        (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent)))
      (mul_nonneg (errorForwardConstant_nonnegative admissible grade) (errorCoefficientSize_nonnegative data (grade + 1))))
  have total := bound.trans (mul_le_mul product (completedTransfer_bound smooth grade large)
    (ContinuousLinearMap.opNorm_nonneg (completedTransfer smooth grade large))
    (mul_nonneg (mul_nonneg (errorForwardConstant_nonnegative admissible grade)
      (errorCoefficientSize_nonnegative data (grade + 1))) (reconstructionBoundConstant_nonnegative admissible grade)))
  exact (congrArg norm (completedRows_difference_factorization admissible data coherent smooth grade large)).le.trans total

end Grad.GaugeCoefficients.Physical.Compensated
