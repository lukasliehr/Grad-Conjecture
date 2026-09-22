import AKAH1SameCartesianMeasurability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualCartesianIntegrability
open Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryLift
open Grad.ActualSmoothPhysicalField Grad.ActualPuncturedFamily Grad.AnnularRestriction Grad.AnnularCurrentLow
open Grad.AnnularClosedJointRegularity Grad.SourceCollarFullSource Grad.BoundaryTrace

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow dimension (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second)=rows first)

open Grad.ActualCartesianDescent Grad.DiskExtension.Operator Grad.PhysicalAxisEquation
include compatible

open Grad.WeightedAxisRemoval

theorem sameCartesianCell_polar_continuousSlices (cell : ℤ) (radius : ℝ) (inside : radius ∈ Ioc (0 : ℝ) 1) :
    Continuous (fun polar => gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell (spatialPlaneOfPair (polarCoord.symm (radius,polar)))) := by
  let index := selectedInnerCollar lower cofinal radius inside.1
  have localInside : radius ∈ Icc (lower index) 1 := ⟨(selectedInnerCollar_lt lower cofinal radius inside.1).le,inside.2⟩
  have equal : (fun polar => gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell (spatialPlaneOfPair (polarCoord.symm (radius,polar)))) =
      fun polar => angularCoefficient (fun axial => (curves index).fullField (bounded index) (radius,polar,axial)) cell := by
    funext polar
    calc
      _ = (curves index).cartesianCellField (bounded index) cell (spatialPlaneOfPair (polarCoord.symm (radius,polar))) :=
        gluedCartesianCellField_same parameters lower positive bounded cofinal decreasing rows curves compatible cell index
          (spatialPlaneOfPair (polarCoord.symm (radius,polar)))
          (by simpa only [spatialPlaneOfPair_polar_norm radius polar inside.1.le] using localInside)
      _ = _ := (curves index).cartesianCellField_actual (bounded index) cell radius localInside polar
  rw [equal]
  exact Grad.SourceCollarFullSource.angularCoefficient_continuous_parameter
    _ ((curves index).fullField_continuous_angles (bounded index) radius localInside) cell

theorem sameCartesianCell_coefficients (cell : ℤ) (radius : ℝ) (inside : radius ∈ Ioc (0 : ℝ) 1) (mode : ℤ) :
    angularCoefficient (fun polar => gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell (spatialPlaneOfPair (polarCoord.symm (radius,polar)))) mode =
      gluedPhysicalFamilyCurve parameters lower positive bounded cofinal rows curves 0 radius (mode,cell) :=
  gluedCartesianCellField_coefficient parameters lower positive bounded cofinal decreasing rows curves compatible cell (selectedInnerCollar lower cofinal radius inside.1) radius
    ⟨(selectedInnerCollar_lt lower cofinal radius inside.1).le,inside.2⟩ mode

/-- Genuine original low-rho row energy gives both Cartesian integrability
bounds for the SAME reconstructed cell, including the required inverse radius. -/
theorem sameOriginalPhysicalCell_integrable_pair (K : ℝ) (estimate : ∀ index,‖rows index‖ ≤ K) (cell : ℤ) :
    IntegrableOn (gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell) openUnitDisk ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell point‖) openUnitDisk := by
  apply originalEnergy_cartesian_integrable_pair parameters lower positive decreasing cofinal rows
    (gluedPhysicalFamilyCurve parameters lower positive bounded cofinal rows curves 0) (samePhysicalCurve_original_ae parameters lower positive bounded cofinal decreasing rows curves compatible) K estimate
    ((samePhysicalCurve_continuous parameters lower positive bounded cofinal decreasing rows curves compatible 0).aestronglyMeasurable measurableSet_Ioc)
    cell (gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell) (sameCartesianCell_aestronglyMeasurable parameters lower positive bounded cofinal decreasing rows curves compatible cell)
    (sameCartesianCell_polar_aestronglyMeasurable parameters lower positive bounded cofinal decreasing rows curves compatible cell)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius inside
    exact sameCartesianCell_polar_continuousSlices parameters lower positive bounded cofinal decreasing rows curves compatible cell radius inside
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius inside
    exact sameCartesianCell_coefficients parameters lower positive bounded cofinal decreasing rows curves compatible cell radius inside

end Grad.ActualCartesianIntegrability
