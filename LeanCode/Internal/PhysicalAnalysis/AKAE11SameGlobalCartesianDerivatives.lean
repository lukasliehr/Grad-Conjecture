import AKAE10ActualSourceCartesianRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualCartesianDescent
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

open Grad.PhysicalFamily Grad.DiskExtension.Operator
include compatible

/-- Exact equality of Cartesian derivatives on every strict inner collar. -/
theorem gluedCartesianFamilyField_fderiv_same (index : ℕ) (point : SpatialPlane × ℝ)
    (inside : ‖point.1‖ ∈ Ioo (lower index) 1) :
    fderiv ℝ (gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves) point =
      fderiv ℝ ((curves index).cartesianField (bounded index)) point := by
  have neighborhood : {current : SpatialPlane × ℝ | ‖current.1‖ ∈ Ioo (lower index) 1} ∈ 𝓝 point :=
    (isOpen_Ioo.preimage (continuous_norm.comp continuous_fst)).mem_nhds inside
  have same : (gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves) =ᶠ[𝓝 point]
      (curves index).cartesianField (bounded index) := by
    filter_upwards [neighborhood] with current member
    exact gluedCartesianFamilyField_same parameters lower positive bounded cofinal decreasing rows curves compatible index current ⟨member.1.le,member.2.le⟩
  exact same.fderiv_eq

theorem gluedCartesianFamilyField_radial_hasDerivAt (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Ioo (lower index) 1) (polar axial : ℝ) :
    HasDerivAt (fun current => (curves index).fullField (bounded index) (current,polar,axial))
      (fderiv ℝ (gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves) (polarPlane (radius,polar),axial) (radialDirection polar,0)) radius := by
  rw [gluedCartesianFamilyField_fderiv_same parameters lower positive bounded cofinal decreasing rows curves compatible index _
    (by simpa only [polarPlane_norm,abs_of_pos ((positive index).trans inside.1)] using inside)]
  exact cartesianPhysicalField_radial_hasDerivAt ((curves index).fullField (bounded index)) (lower index) 1
    (((curves index).fullField_smooth (bounded index)).mono (fun _ member => ⟨⟨member.1.1.le,member.1.2.le⟩,member.2⟩))
    (fun radius axial => (curves index).fullField_angular_periodic (bounded index) radius axial)
    radius ((positive index).trans inside.1) inside polar axial

theorem gluedCartesianFamilyField_angular_hasDerivAt (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Ioo (lower index) 1) (polar axial : ℝ) :
    HasDerivAt (fun current => (curves index).fullField (bounded index) (radius,current,axial))
      (fderiv ℝ (gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves) (polarPlane (radius,polar),axial) (radius • planeQuarterTurn (radialDirection polar),0)) polar := by
  rw [gluedCartesianFamilyField_fderiv_same parameters lower positive bounded cofinal decreasing rows curves compatible index _
    (by simpa only [polarPlane_norm,abs_of_pos ((positive index).trans inside.1)] using inside)]
  exact cartesianPhysicalField_angular_hasDerivAt ((curves index).fullField (bounded index)) (lower index) 1
    (((curves index).fullField_smooth (bounded index)).mono (fun _ member => ⟨⟨member.1.1.le,member.1.2.le⟩,member.2⟩))
    (fun radius axial => (curves index).fullField_angular_periodic (bounded index) radius axial)
    radius ((positive index).trans inside.1) inside polar axial

theorem gluedCartesianFamilyField_axial_hasDerivAt (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Ioo (lower index) 1) (polar axial : ℝ) :
    HasDerivAt (fun current => (curves index).fullField (bounded index) (radius,polar,current))
      (fderiv ℝ (gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves) (polarPlane (radius,polar),axial) (0,1)) axial := by
  rw [gluedCartesianFamilyField_fderiv_same parameters lower positive bounded cofinal decreasing rows curves compatible index _
    (by simpa only [polarPlane_norm,abs_of_pos ((positive index).trans inside.1)] using inside)]
  exact cartesianPhysicalField_axial_hasDerivAt ((curves index).fullField (bounded index)) (lower index) 1
    (((curves index).fullField_smooth (bounded index)).mono (fun _ member => ⟨⟨member.1.1.le,member.1.2.le⟩,member.2⟩))
    (fun radius axial => (curves index).fullField_angular_periodic (bounded index) radius axial)
    radius ((positive index).trans inside.1) inside polar axial

/-- A global cell is literally the axial Fourier integral of the same
complete global Cartesian field, with every angular mode retained. -/
theorem gluedCartesianCellField_actual_polar (cell : ℤ) (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc (lower index) 1) (polar : ℝ) :
    gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell
      (spatialPlaneOfPair (polarCoord.symm (radius,polar))) =
    angularCoefficient (fun axial => gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves
      (spatialPlaneOfPair (polarCoord.symm (radius,polar)),axial)) cell := by
  have normInside : ‖spatialPlaneOfPair (polarCoord.symm (radius,polar))‖ ∈ Icc (lower index) 1 := by
    simpa only [spatialPlaneOfPair_polar_norm radius polar ((positive index).le.trans inside.1)] using inside
  have sameFull : (fun axial => gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves
      (spatialPlaneOfPair (polarCoord.symm (radius,polar)),axial)) =
      fun axial => (curves index).fullField (bounded index) (radius,polar,axial) := by
    funext axial
    calc
      _ = (curves index).cartesianField (bounded index)
          (spatialPlaneOfPair (polarCoord.symm (radius,polar)),axial) :=
        gluedCartesianFamilyField_same parameters lower positive bounded cofinal decreasing rows curves compatible
          index (spatialPlaneOfPair (polarCoord.symm (radius,polar)),axial) normInside
      _ = _ := (curves index).cartesianField_polar (bounded index) radius
          ((positive index).trans_le inside.1) polar axial
  rw [sameFull]
  calc
    _ = (curves index).cartesianCellField (bounded index) cell
        (spatialPlaneOfPair (polarCoord.symm (radius,polar))) :=
      gluedCartesianCellField_same parameters lower positive bounded cofinal decreasing rows curves compatible
        cell index (spatialPlaneOfPair (polarCoord.symm (radius,polar))) normInside
    _ = _ := (curves index).cartesianCellField_actual (bounded index) cell radius inside polar

end Grad.ActualCartesianDescent
