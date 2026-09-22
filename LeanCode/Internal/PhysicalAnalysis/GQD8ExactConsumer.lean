import GQD7ActualLowBall

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation

variable {L sigma gamma ell : ℝ} {admissible : Admissible L sigma gamma ell}
  {gauge : CoefficientFamily L sigma gamma ell 3 3}

/-- Exact AN8 for every completed point: the SAME five Hilbert slots,
not a replacement product norm or an independent maximal weak graph. -/
theorem compensatedClosure_norm_sq (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    ‖field‖ ^ 2 = ‖field.val 0‖ ^ 2 + ‖field.val 1‖ ^ 2 + ‖field.val 2‖ ^ 2 +
      ‖field.val 3‖ ^ 2 + ‖field.val 4‖ ^ 2 :=
  (PiLp.norm_sq_eq_of_L2
    (fun index : Fin 5 => apGrade L sigma gamma ell (graphDimension index) (graphGrade grade index))
    field.val).trans (sum_fin_five (fun index => ‖field.val index‖ ^ 2))

theorem completedTransfer_literal_core
    (smooth : SmoothCompensatedCoreIsomorphism admissible gauge)
    (grade : ℕ) (large : 3 ≤ grade) (core : circularCompensatedCore admissible) :
    (completedTransfer smooth grade large (compensatedIntoClosure admissible grade _ core)).val =
      compensatedGraphLinear admissible grade
        (compensatedForward admissible gauge smooth.coherent smooth.inverseCoherent core.val) := by
  exact (congrArg Subtype.val (completedTransfer_core smooth grade large core)).trans
    (congrArg (compensatedGraphLinear admissible grade) (smooth.forward core))

theorem completedInverse_literal_core
    (smooth : SmoothCompensatedCoreIsomorphism admissible gauge)
    (grade : ℕ) (core : currentCompensatedCore admissible gauge smooth.coherent) :
    (completedInverse smooth grade (compensatedIntoClosure admissible grade _ core)).val =
      compensatedGraphLinear admissible grade (compensatedBackward L sigma gamma ell core.val) := by
  exact (congrArg Subtype.val (completedInverse_core smooth grade core)).trans
    (congrArg (compensatedGraphLinear admissible grade) (smooth.backward core))

/-- The fixed inverse bound has no ell, coefficient, seed or high-grade
smallness dependence. Both inverse identities hold on ALL completed points. -/
theorem completedTransferConsumer
    (smooth : SmoothCompensatedCoreIsomorphism admissible gauge)
    (grade : ℕ) (large : 3 ≤ grade) :
    Function.LeftInverse (completedInverse smooth grade) (completedTransfer smooth grade large) ∧
    Function.RightInverse (completedInverse smooth grade) (completedTransfer smooth grade large) ∧
    ‖completedTransfer smooth grade large‖ ≤ completedTransferConstant gauge grade ∧
    ‖completedInverse smooth grade‖ ≤ backwardDifferenceConstant grade + 1 ∧
    ‖completedTransferDifference smooth grade large‖ ≤
      (transferPolynomial L sigma gamma grade).eval (gaugeEpsilon (gauge (grade + 3))) :=
  ⟨completedTransfer_left_inverse smooth grade large, completedTransfer_right_inverse smooth grade large,
    completedTransfer_bound smooth grade large, completedInverse_bound smooth grade,
    completedTransferDifference_bound smooth grade large⟩

theorem actualCompensatedClosureConsumer (parameters : PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold) :
    ActualCompensatedClosureGoal parameters L radius threshold :=
  actualCompensatedClosure parameters L radius threshold positive radiusNonnegative thresholdPositive

end Grad.GaugeCoefficients.Physical.Compensated
