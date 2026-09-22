import GQD8ExactConsumer
import GQD9GraphRealization

noncomputable section
set_option maxHeartbeats 800000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.GaugeTransfer

variable {L sigma gamma ell : ℝ} {admissible : Admissible L sigma gamma ell}
  {gauge : CoefficientFamily L sigma gamma ell 3 3}

theorem completedTransfer_actual_rotation
    (smooth : SmoothCompensatedCoreIsomorphism admissible gauge) (grade : ℕ) (large : 3 ≤ grade)
    (field : circularCompensatedClosure admissible grade) :
    APHasAngularDerivative L sigma gamma ell
      ((completedTransfer smooth grade large field).val 1)
      ((completedTransfer smooth grade large field).val 2) ∧
    APHasAngularDerivative L sigma gamma ell
      ((completedTransfer smooth grade large field).val 3)
      ((completedTransfer smooth grade large field).val 4) :=
  ⟨compensatedClosure_planarRotation admissible grade _ _, compensatedClosure_scalarRotation admissible grade _ _⟩

theorem completedTransfer_faithful_fields
    (smooth : SmoothCompensatedCoreIsomorphism admissible gauge) (grade : ℕ) (large : 3 ≤ grade)
    (field : circularCompensatedClosure admissible grade)
    (theta : (completedTransfer smooth grade large field).val 0 = 0)
    (planar : (completedTransfer smooth grade large field).val 1 = 0)
    (scalar : (completedTransfer smooth grade large field).val 3 = 0) : field = 0 := by
  have imageZero := compensatedClosure_zero_of_fields_zero admissible grade
    (currentCompensatedCore admissible gauge smooth.coherent) (completedTransfer smooth grade large field) theta planar scalar
  have original := congrArg (completedInverse smooth grade) imageZero
  exact (completedTransfer_left_inverse smooth grade large field).symm.trans (original.trans (map_zero _))

end Grad.GaugeCoefficients.Physical.Compensated
