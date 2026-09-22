import ASR2AllRadialRobin

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualSmoothRobin
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.ActualOuterCollar Grad.SourceCollarRestriction
open Grad.SourceCollarDivision Grad.BoundaryTrace Grad.NonlinearRange

theorem radialFirst_boundary_euler (solution : ClosedJet 1) (angle : ℝ) :
    radialIter 1 (originalPolarValue solution) (1, angle) =
      (eulerJet solution).value (boundaryDiskPoint (angle : CellCircle)) := by
  change radialField (smoothClosedExtension solution ∘ polarPlane) (1, angle) = _
  rw [polar_radial_first _ (smoothClosedExtension_smooth solution), eulerJet_extension_value]
  have pointLaw : (boundaryDiskPoint (angle : CellCircle)).val = radialDirection angle :=
    boundaryCirclePoint_coe angle
  rw [pointLaw, polarPlane_eq, one_smul]

theorem radialSlope_boundary_fourier (solution : ClosedJet 1) (mode : ℤ) :
    radialCoefficientJet (originalPolarValue solution) mode 1 1 =
      diskBoundaryFourier (diskCoreInto (eulerJet solution)) (mode, 0) := by
  have functions : (fun angle => radialIter 1 (originalPolarValue solution) (1, angle)) =
      (fun angle : ℝ => (eulerJet solution).value (boundaryDiskPoint (angle : CellCircle))) :=
    funext (radialFirst_boundary_euler solution)
  change angularCoefficient (fun angle => radialIter 1 (originalPolarValue solution) (1, angle)) mode = _
  exact (congrArg (fun value : ℝ → ComplexEuclidean 1 => angularCoefficient value mode) functions).trans
    ((angularCoefficient_circle (fun angle : CellCircle => (eulerJet solution).value (boundaryDiskPoint angle)) mode).trans
      (diskBoundaryFourier_core_cell (eulerJet solution) mode).symm)

/-- The literal outward Robin row on the unit circle. -/
def robinResidualJet (solution : ClosedJet 1) : ClosedJet 1 :=
  eulerJet solution + (2 : ℂ) • solution

theorem robinResidual_boundary_fourier (solution : ClosedJet 1) (mode : ℤ) :
    diskBoundaryFourier (diskCoreInto (robinResidualJet solution)) (mode, 0) =
      radialCoefficientJet (originalPolarValue solution) mode 1 1 +
        (2 : ℝ) • radialCoefficientJet (originalPolarValue solution) mode 0 1 := by
  let trace : ClosedJet 1 →ₗ[ℂ] ComplexEuclidean 1 :=
    (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 (mode, 0)).toLinearMap.comp
      (diskBoundaryFourier.toLinearMap.comp diskCoreInto)
  have expanded := trace.map_add (eulerJet solution) ((2 : ℂ) • solution)
  have scaled := trace.map_smul (2 : ℂ) solution
  change trace (eulerJet solution + (2 : ℂ) • solution) = _
  rw [expanded, scaled]
  change diskBoundaryFourier (diskCoreInto (eulerJet solution)) (mode, 0) +
      (2 : ℂ) • diskBoundaryFourier (diskCoreInto solution) (mode, 0) = _
  have value := diskCoreRadialCurve_boundary mode solution
  change radialCoefficientJet (originalPolarValue solution) mode 0 1 = _ at value
  exact congrArg₂ (fun first second : ComplexEuclidean 1 => first + (2 : ℝ) • second)
    (radialSlope_boundary_fourier solution mode).symm value.symm

theorem sameH1_robin_boundary_coefficients (parameter : ℝ) (source : highDiskL2) (solution : ClosedJet 1)
    (same : diskCoreInto solution = (highRobinWeakInverse parameter source).val) :
    diskBoundaryFourier (diskCoreInto (robinResidualJet solution)) = 0 := by
  apply lp.ext
  funext index
  rcases index with ⟨mode, cell⟩
  by_cases zero : cell = 0
  · subst cell
    exact (robinResidual_boundary_fourier solution mode).trans
      (sameH1_all_radial_robin parameter source solution same mode)
  · exact diskBoundaryFourier_core_zero _ mode cell zero

end Grad.ActualSmoothRobin
