import AKBB8ActualPrimitiveDeterminantSlope

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarFlux
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularSmoothCore Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.ActualPolarEquations

/-- Existing all-grade jets reconstruct the genuine scalar radial equation
from exact coefficients, preserving the SAME full physical field. -/
theorem fullScalarField_radial_of_doubleCoefficients {parameters : PhaseParameters}
    {lower : ℝ} {positive : 0 < lower} {row : DivisionRow 1 lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower < 1)
    (radius : ℝ) (inside : radius ∈ Icc lower 1)
    (slope : (ℤ × ℤ) → ComplexEuclidean 1)
    (derivatives : ∀ mode, HasDerivWithinAt (fun current => curves.physicalCurve 0 current mode) (slope mode) (Icc lower 1) radius)
    (rhs : ℝ × ℝ → ComplexEuclidean 1) (continuousRHS : Continuous rhs)
    (angular : ∀ axial, Function.Periodic (fun polar => rhs (polar,axial)) (2 * Real.pi))
    (cell : ∀ polar, Function.Periodic (fun axial => rhs (polar,axial)) (2 * Real.pi))
    (coefficients : ∀ mode, doubleCoefficient rhs mode = slope mode) (angles : ℝ × ℝ) :
    HasDerivWithinAt (fun current => curves.fullField bounded (current,angles))
      (rhs angles) (Icc lower 1) radius := by
  have given := hilbertPhysicalField_radial_of_doubleCoefficients lower positive bounded
    curves.physicalCurve (curves.physicalCurve_smooth bounded)
    (fun grade current member mode => by
      rw [curves.physicalCurve_grade bounded grade current member mode,Complex.ofReal_pow]
      rfl)
    radius inside slope derivatives rhs continuousRHS angular cell coefficients angles
  have same (current : ℝ) (member : current ∈ Icc lower 1) :
      curves.fullField bounded (current,angles) = hilbertPhysicalField lower bounded curves.physicalCurve (current,angles) := by
    rw [fullField_scalarSeries curves bounded current member angles]
    simp only [hilbertPhysicalField,radialClamp_eq lower bounded.le current member]
  apply given.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with current member
    exact same current member
  · exact same radius inside

end Grad.ActualPolarFlux
