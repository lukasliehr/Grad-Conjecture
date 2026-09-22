import GQE16ExactConsumer

noncomputable section
set_option maxHeartbeats 500000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.GaugeTransfer

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)

def completedThetaLowered (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] apGrade L sigma gamma ell 1 (grade + 1) :=
  (apLowering L sigma gamma ell (by omega : grade + 1 ≤ grade + 2)).comp
    (compensatedClosureEntry admissible grade core 0)

/-- The completed ψ is genuinely RΘ in the accepted original weak
realization; it cannot acquire an independent derivative coordinate. -/
theorem completedPsi_actual_rotation (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (field : compensatedClosure admissible grade core) :
    APHasAngularDerivative L sigma gamma ell
      (completedThetaLowered admissible grade core field) (completedPsi admissible grade core field) := by
  apply angularDerivative_of_dense (compensatedIntoClosure admissible grade core)
    (compensatedIntoClosure_denseRange admissible grade core)
    (completedThetaLowered admissible grade core) (completedPsi admissible grade core) _ field
  intro data
  have value : completedThetaLowered admissible grade core (compensatedIntoClosure admissible grade core data) =
      apSmoothGrade L sigma gamma ell 1 (grade + 1) data.val.1 :=
    data.val.1.property (grade + 1) (grade + 2) (by omega)
  have derivative := completedPsi_core admissible grade core data
  intro cell testCell vector test smooth compact supported
  have differentiated := congrArg (fun input : apGrade L sigma gamma ell 1 (grade + 1) =>
    apDiskPairing 1 testCell vector test smooth compact (apL2Trace L sigma gamma ell cell input)) derivative
  have undifferentiated := congrArg (fun input : apGrade L sigma gamma ell 1 (grade + 1) =>
    angularWeakPairing 1 testCell vector test smooth compact (apL2Trace L sigma gamma ell cell input)) value
  exact differentiated.trans
    ((apSmoothRotation_weak admissible data.val.1 (grade + 1) cell testCell vector test smooth compact supported).trans
      undifferentiated.symm)

theorem completedPsi_unique_rotation (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (field : compensatedClosure admissible grade core)
    (other : apGrade L sigma gamma ell 1 (grade + 1))
    (genuine : APHasAngularDerivative L sigma gamma ell (completedThetaLowered admissible grade core field) other) :
    other = completedPsi admissible grade core field :=
  genuine.unique (completedPsi_actual_rotation admissible grade core field)

end Grad.GaugeCoefficients.Physical.Compensated
