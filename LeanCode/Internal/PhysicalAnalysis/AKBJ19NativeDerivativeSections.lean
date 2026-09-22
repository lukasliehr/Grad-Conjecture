import AKBK7OriginalForceAngularContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 250000
open Set
open scoped ContDiff
namespace Grad.ActualScalarWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceBoundaryTrace Grad.BoundaryTrace
open Grad.SourceCollarCoefficients Grad.ActualCartesianEquations Grad.PDEBootstrap Grad.SourceCollarFullSource
open Grad.ActualCartesianDescent Grad.ActualSmoothPhysicalField Grad.SourceCollarDivision
open Grad.ActualCartesianWeakEquations

/-- The axial section of a genuine joint derivative, with the direction fixed before specializing the source family. -/
theorem originalDerivative_axialContinuous {dimension : ℕ} (field : Spatial × ℝ → ComplexEuclidean dimension)
    (radius : ℝ) (continuousDerivative : Continuous (fun angles : ℝ × ℝ =>
      fderiv ℝ field (polarPlane (radius,angles.1),angles.2))) (polar : ℝ) (direction : Spatial × ℝ) :
    Continuous (fun axial : ℝ => fderiv ℝ field (polarPlane (radius,polar),axial) direction) := by
  have axialSection : Continuous (fun axial : ℝ => fderiv ℝ field (polarPlane (radius,polar),axial)) :=
    by simpa only [Function.comp_def] using continuousDerivative.comp (show Continuous (fun axial : ℝ => (polar,axial)) from continuous_const.prodMk continuous_id)
  exact axialSection.clm_apply (show Continuous (fun _ : ℝ => direction) from continuous_const)


end Grad.ActualScalarWeakEquations
