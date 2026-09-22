import AKCJ6ActualSameRetainedScalarCore
import AKCJ7OriginalCoreProductRotation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange
open Grad.SourceCollarFullSource Grad.SourceCollarDivision Grad.ActualCartesianDescent Grad.BoundaryTrace

/-- SAME original core values in polar coordinates identify the complete
Cartesian field on the same closed collar. -/
theorem originalCore_field_of_polar {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (lower : ℝ) (positive : 0<lower)
    (field : SpatialPlane×ℝ→ComplexEuclidean dimension)
    (same : ∀ (radius : ℝ) (inside : radius∈Icc lower 1) (angles : ℝ×ℝ),
      coreValue core (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) angles.2=
        field (polarPlane (radius,angles.1),angles.2))
    (point : SpatialPlane×ℝ) (inside : ‖point.1‖∈Icc lower 1) :
    coreValue core ⟨point.1,inside.2⟩ point.2=field point := by
  let closed : ClosedDisk := ⟨point.1,inside.2⟩
  obtain ⟨angle,polar⟩ := closedPoint_has_polar_angle closed
  have divisionPoint : Grad.SourceCollarDivision.polarClosedPoint ‖point.1‖ angle
      (positive.le.trans inside.1) inside.2=closed := by
    rw [divisionPolarPoint_eq_original]
    exact polar
  have coordinates : polarPlane (‖point.1‖,angle)=point.1 := congrArg Subtype.val divisionPoint
  have value := same ‖point.1‖ inside (angle,point.2)
  rw [divisionPoint] at value
  change coreValue core closed point.2=field (polarPlane (‖point.1‖,angle),point.2) at value
  rw [coordinates] at value
  exact value

/-- Genuine derivatives of the SAME full Cartesian field follow from values;
no derivative compatibility premise is needed. -/
theorem originalCore_fderiv_of_polar {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (lower : ℝ) (positive : 0<lower)
    (field : SpatialPlane×ℝ→ComplexEuclidean dimension)
    (same : ∀ (radius : ℝ) (inside : radius∈Icc lower 1) (angles : ℝ×ℝ),
      coreValue core (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) angles.2=
        field (polarPlane (radius,angles.1),angles.2))
    (point : SpatialPlane×ℝ) (inside : ‖point.1‖∈Ioo lower 1) :
    fderiv ℝ (originalCoreProductLift parameters core) point=fderiv ℝ field point :=
  originalCoreProductLift_annular_fderiv parameters core lower field
    (originalCore_field_of_polar parameters core lower positive field same) point inside

end Grad.OriginalCoreRealization
