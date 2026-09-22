import AKCA18ActualOriginalScalarMean

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.ActualPhysicalField Grad.AnnularCurrentSource Grad.AnnularCurrentLow
open Grad.AnnularSourceGraph Grad.AnnularKnownLow Grad.SourceCollarFullSource Grad.BoundaryTrace Grad.AnnularVariational

variable {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower} {row : DivisionRow 1 lower}

def scalarRadiusCurves (curves : SmoothLowPhysicalRow parameters lower positive row) :
    SmoothLowPhysicalRow parameters lower positive (radialRadiusRow lower positive row) where
  curve grade radius := radius • curves.curve grade radius
  smooth grade := contDiffOn_id.smul (curves.smooth grade)
  same grade := by
    filter_upwards [curves.same grade,radialRadiusRow_ae lower positive row] with radius same weighted
    intro mode
    change radius • curves.curve grade radius mode=_
    rw [same mode]
    unfold lowRhoPhysicalCoefficient
    rw [weighted mode]
    simp only [smul_comm _ radius]

 theorem scalarRadiusCurves_fullField (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower<1) (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ×ℝ) :
    (scalarRadiusCurves curves).fullField bounded (radius,angles)=radius • curves.fullField bounded (radius,angles) := by
  apply congrFun ((scalarRadiusCurves curves).fullField_eq_of_doubleCoefficient bounded radius inside _
    ((curves.fullField_continuous_angles bounded radius inside).const_smul radius)
    (fun axial polar => congrArg (radius • ·) (curves.fullField_angular_periodic bounded radius axial polar))
    (fun polar axial => congrArg (radius • ·) (curves.fullField_cell_periodic bounded radius polar axial)) _) angles
  intro mode
  have scalarLaw : doubleCoefficient (fun angles => radius • curves.fullField bounded (radius,angles)) mode=
      radius • doubleCoefficient (fun angles => curves.fullField bounded (radius,angles)) mode := by
    simpa only [smul_apply,ContinuousLinearMap.id_apply,Complex.coe_smul] using
      doubleCoefficient_valueMap ((radius : ℂ) • ContinuousLinearMap.id ℂ (ComplexEuclidean 1)) _
        (curves.fullField_continuous_angles bounded radius inside) mode
  change doubleCoefficient (fun angles => radius • curves.fullField bounded (radius,angles)) mode=_
  rw [scalarLaw,curves.fullField_doubleCoefficient bounded radius inside mode,
    (scalarRadiusCurves curves).physicalCurve_coefficient bounded 0 radius inside mode,
    curves.physicalCurve_coefficient bounded 0 radius inside mode]
  change radius • (_ • curves.curve 0 radius mode)=_ • (radius • curves.curve 0 radius mode)
  exact smul_comm radius _ _

 theorem scalarRadiusCurves_cartesianField (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower<1) (point : SpatialPlane×ℝ) (inside : ‖point.1‖∈Icc lower 1) :
    (scalarRadiusCurves curves).cartesianField bounded point=‖point.1‖ • curves.cartesianField bounded point := by
  simp only [SmoothLowPhysicalRow.cartesianField,Grad.ActualCartesianDescent.cartesianPhysicalField,
    Grad.ActualCartesianDescent.cartesianFromPolar,Grad.BoundaryLift.complexCoordinate_norm]
  exact scalarRadiusCurves_fullField curves bounded ‖point.1‖ inside _

end Grad.OriginalCoreRealization
