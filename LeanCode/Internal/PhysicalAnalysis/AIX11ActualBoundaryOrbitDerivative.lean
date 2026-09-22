import AIX10ActualOperatorOrbitDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularKernelOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction

variable {src tgt : ℕ} (parameters : PhaseParameters) (traceAngular traceCell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters src tgt)

def boundaryOrbitJetAction (tau : OrbitParameter) (angular cell : ℕ) :
    NegativeTrace parameters traceAngular traceCell src →L[ℂ] NegativeTrace parameters traceAngular traceCell tgt :=
  fullNegativeKernelAction parameters traceAngular traceCell (kernelOrbitJet tau angular cell kernel)

theorem boundaryOrbitJetAction_norm_le (tau : OrbitParameter) (angular cell : ℕ) :
    ‖boundaryOrbitJetAction parameters traceAngular traceCell kernel tau angular cell‖ ≤
      fullKernelMoment parameters (traceAngular + traceCell + 1 + (angular + cell)) kernel :=
  (fullNegativeKernelAction_norm_le parameters traceAngular traceCell _).trans
    (kernelOrbitJet_moment_le tau angular cell kernel _)

theorem boundaryOrbitJetAction_remainder_bound (tau step : OrbitParameter) (angular cell : ℕ) :
    ‖boundaryOrbitJetAction parameters traceAngular traceCell kernel (tau + step) angular cell -
      boundaryOrbitJetAction parameters traceAngular traceCell kernel tau angular cell -
      (step.1 : ℂ) • boundaryOrbitJetAction parameters traceAngular traceCell kernel tau (angular + 1) cell -
      (step.2 : ℂ) • boundaryOrbitJetAction parameters traceAngular traceCell kernel tau angular (cell + 1)‖ ≤
        3 * orbitStepSize step ^ 2 *
          fullKernelMoment parameters (traceAngular + traceCell + 1 + (angular + cell + 2)) kernel := by
  have equality : fullNegativeKernelAction parameters traceAngular traceCell
      (kernelOrbitRemainder tau step angular cell kernel) =
      boundaryOrbitJetAction parameters traceAngular traceCell kernel (tau + step) angular cell -
      boundaryOrbitJetAction parameters traceAngular traceCell kernel tau angular cell -
      (step.1 : ℂ) • boundaryOrbitJetAction parameters traceAngular traceCell kernel tau (angular + 1) cell -
      (step.2 : ℂ) • boundaryOrbitJetAction parameters traceAngular traceCell kernel tau angular (cell + 1) := by
    apply ContinuousLinearMap.ext
    intro field
    rw [kernelOrbitRemainder_identity, fullNegativeKernelAction_sub, fullNegativeKernelAction_sub,
      fullNegativeKernelAction_sub, fullNegativeKernelAction_smul, fullNegativeKernelAction_smul]
    rfl
  rw [← equality]
  exact (fullNegativeKernelAction_norm_le parameters traceAngular traceCell _).trans
    (kernelOrbitRemainder_moment_le tau step angular cell kernel _)

/-- A genuine boundary operator Fréchet derivative at every original
negative-half grade, with the same analytic width. -/
theorem boundaryOrbitJetAction_hasFDerivAt (tau : OrbitParameter) (angular cell : ℕ) :
    HasFDerivAt (fun sigma => boundaryOrbitJetAction parameters traceAngular traceCell kernel sigma angular cell)
      (orbitDifferential
        (boundaryOrbitJetAction parameters traceAngular traceCell kernel tau (angular + 1) cell)
        (boundaryOrbitJetAction parameters traceAngular traceCell kernel tau angular (cell + 1))) tau :=
  hasFDerivAt_of_orbitRemainder _ tau _ _ _ (fullKernelMoment_nonnegative _ _ _)
    (fun step => boundaryOrbitJetAction_remainder_bound parameters traceAngular traceCell kernel tau step angular cell)

end Grad.AnnularKernelOrbit
