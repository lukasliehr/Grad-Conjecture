import AKAC19FullPhysicalFieldLinearity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryLift Grad.PhaseAlgebra

variable {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1)

theorem SmoothLowPhysicalRow.fullField_meanFree (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    curves.meanFree.fullField bounded (radius,angles) =
      removePolarMean (fun angles => curves.fullField bounded (radius,angles)) angles := by
  apply congrFun (curves.meanFree.fullField_eq_of_doubleCoefficient bounded radius inside _
    (removePolarMean_continuous _ (curves.fullField_continuous_angles bounded radius inside)) _ _ _) angles
  · intro axial polar
    change curves.fullField bounded (radius,polar+2*Real.pi,axial) - _ = _
    rw [curves.fullField_angular_shift bounded radius polar axial]
    rfl
  · intro polar axial
    unfold removePolarMean
    change curves.fullField bounded (radius,polar,axial+2*Real.pi) -
      angularCoefficient (fun angle => curves.fullField bounded (radius,angle,axial+2*Real.pi)) 0 = _
    rw [curves.fullField_cell_shift bounded radius polar axial]
    congr 1
    exact congrArg (fun field : ℝ → ComplexEuclidean 1 => angularCoefficient field 0)
      (funext (fun angle => curves.fullField_cell_periodic bounded radius angle axial))
  · intro mode
    rw [show doubleCoefficient (removePolarMean (fun angles => curves.fullField bounded (radius,angles))) mode =
      if mode.1=0 then 0 else doubleCoefficient (fun angles => curves.fullField bounded (radius,angles)) mode from
        doubleCoefficient_removePolarMean _ (curves.fullField_continuous_angles bounded radius inside) mode,
      curves.fullField_doubleCoefficient bounded radius inside mode,
      curves.meanFree.physicalCurve_coefficient bounded 0 radius inside mode,
      curves.physicalCurve_coefficient bounded 0 radius inside mode]
    change (if mode.1=0 then 0 else _) = _ • ((if mode.1=0 then (0 : ℂ) else 1) • curves.curve 0 radius mode)
    split_ifs <;> simp

/-- The reconstructed original scalar divided by radius is exactly Xi/r
plus P(a_c,2), on the SAME full periodic physical field. -/
theorem SmoothLowPhysicalRow.fullField_polarScalarOverRadius
    {polar : DivisionRow 3 lower} (covariant : SmoothLowPhysicalRow parameters lower positive polar)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.polarScalarOverRadius covariant).fullField bounded (radius,angles) =
      curves.fullField bounded (radius,angles) +
        removePolarMean (fun query => matrixUnit (0 : Fin 1) (1 : Fin 3)
          (covariant.fullField bounded (radius,query))) angles := by
  change (curves.add (covariant.bulkUnit (0 : Fin 1) 1).meanFree).fullField bounded (radius,angles) = _
  rw [curves.fullField_add bounded _ radius inside angles,
    (covariant.bulkUnit (0 : Fin 1) 1).fullField_meanFree bounded radius inside angles]
  congr 1
  congr 1
  funext query
  exact covariant.fullField_bulkUnit bounded (0 : Fin 1) 1 radius inside query

end Grad.ActualSmoothPhysicalField
