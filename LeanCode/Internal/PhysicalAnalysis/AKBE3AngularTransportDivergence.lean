import AKBE2ProjectedForceAxisRemoval

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCartesianWeakEquations
open Grad.PDEBootstrap Grad.RepresentedKernel.SpatialProduct
open Grad.ActualSmoothPhysicalField Grad.PhysicalFamily

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The original angular transport has zero divergence in its coefficient;
its two Cartesian flux derivatives are precisely R of the same field. -/
theorem angularTransportFlux_divergence (field : Spatial → E) (point : Spatial)
    (differentiable : DifferentiableAt ℝ field point) :
    (∑ direction : Fin 2, directionDerivative direction (angularTransportFlux field direction) point) =
      fderiv ℝ field point (planeQuarterTurn point) := by
  have coordinateZero (direction : Fin 2) : angularRotationCoordinate direction (spatialDirection direction) = 0 := by
    fin_cases direction <;> simp [angularRotationCoordinate,spatialDirection]
  have derivative (direction : Fin 2) :
      directionDerivative direction (angularTransportFlux field direction) point =
        angularRotationCoordinate direction point • fderiv ℝ field point (spatialDirection direction) := by
    have given := ((angularRotationCoordinate direction).hasFDerivAt.smul differentiable.hasFDerivAt).fderiv
    have evaluated := congrArg (fun derivative : Spatial →L[ℝ] E => derivative (spatialDirection direction)) given
    have functionSame : (fun current => angularRotationCoordinate direction current • field current) =
        angularTransportFlux field direction := rfl
    change fderiv ℝ (fun current => angularRotationCoordinate direction current • field current) point
      (spatialDirection direction) = _ at evaluated
    rw [functionSame] at evaluated
    simpa [directionDerivative,coordinateZero] using evaluated
  simp_rw [derivative,← map_smul]
  rw [← map_sum]
  congr 1
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [Fin.sum_univ_two,angularRotationCoordinate,spatialDirection,planeQuarterTurn]

/-- Integration by parts for the genuine R flux uses the accepted Cartesian
divergence theorem, so the later physical weak rows keep the exact same R. -/
theorem angularTransportFlux_smooth (domain : Set Spatial) (field : Spatial → E)
    (smooth : ContDiffOn ℝ ∞ field domain) (direction : Fin 2) :
    ContDiffOn ℝ ∞ (angularTransportFlux field direction) domain :=
  (angularRotationCoordinate direction).contDiff.contDiffOn.smul smooth

end Grad.ActualCartesianWeakEquations
