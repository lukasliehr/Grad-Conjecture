import SCS40PhysicalG3Coefficients

noncomputable section

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.Constraints.Gauges

theorem divisionPolarPoint_eq_original (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    polarClosedPoint radius angle nonnegative bounded =
      Grad.Constraints.polarClosedPoint radius (by rwa [abs_of_nonneg nonnegative]) angle := by
  apply Subtype.ext
  rw [Grad.Constraints.polarClosedPoint_coordinates]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [polarClosedPoint, polarPlane, collarPlane]

theorem radialProjection_component (angle : ℝ) (value : ComplexEuclidean 2) :
    radialProjection angle value 0 = Grad.Constraints.polarRadialComponent angle value := by
  simp [radialProjection, planarComponentMap, Grad.Constraints.polarRadialComponent]

theorem tangentialProjection_component (angle : ℝ) (value : ComplexEuclidean 2) :
    tangentialProjection angle value 0 = Grad.Constraints.polarTangentialComponent angle value := by
  simp [tangentialProjection, planarComponentMap, Grad.Constraints.polarTangentialComponent]
  ring

end Grad.SourceCollarFullSource
