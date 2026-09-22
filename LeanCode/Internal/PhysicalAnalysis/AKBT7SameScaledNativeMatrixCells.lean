import AKBT6ActualNativeCurrentRecovery
import AKAM1FullMatrixFluxIntegrability
import AKBF12SameScaledStartupFields
import AKBE21RadialProjectionAxialCell

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace Grad.ActualScaledNativeCoefficients
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.BoundaryTrace
open Grad.SourceCollarCoefficients Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.ActualSmoothPhysicalField Grad.ActualCartesianDescent Grad.ActualPuncturedFamily
open Grad.AnnularRestriction Grad.DiskExtension.Operator Grad.SourceCollarFullSource

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index, 0 < lower index) (bounded : ∀ index, lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index, DivisionRow dimension (lower index))
    (curves : ∀ index, SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second) = rows first)
include compatible


open Grad.CartesianStartup Grad.GenericCarriers Grad.SpatialDilation Grad.ActualCartesianWeakEquations
open Grad.ActualCartesianFlux Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
/-- The completed native matrix output is the axial cell of the full
matrix product at the SAME Cartesian point. -/
theorem nativeMatrixCell_actual {output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 dimension output)
    (coherent : FamilyCoherent family) (cell : ℤ) (point : Spatial)
    (nonzero : point ≠ 0) (inside : ‖point‖ < 1) :
    matrixFluxCell parameters family coherent lower positive bounded cofinal rows curves cell point =
      angularCoefficient (fun axial => startupRawMatrix family
        (fun pair => gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves (pair.2,pair.1))
        (axial,point)) cell := by
  let closed : ClosedDisk := ⟨point,inside.le⟩
  obtain ⟨angle,polar⟩ := closedPoint_has_polar_angle closed
  have represented : spatialPlaneOfPair (polarCoord.symm (‖point‖,angle)) = point := by
    rw [polarPlane_originalParametrization]
    have coordinates := congrArg Subtype.val polar
    rw [Grad.Constraints.polarClosedPoint_coordinates] at coordinates
    simpa [polarPlane,collarPlane,closed] using coordinates
  let index := selectedInnerCollar lower cofinal ‖point‖ (norm_pos_iff.mpr nonzero)
  have collar : ‖point‖ ∈ Icc (lower index) 1 :=
    ⟨(selectedInnerCollar_lt lower cofinal ‖point‖ (norm_pos_iff.mpr nonzero)).le,inside.le⟩
  have actual := matrixFluxCell_actual parameters family coherent lower positive bounded cofinal decreasing rows curves compatible
    cell index ‖point‖ collar angle
  rw [represented] at actual
  refine actual.trans ?_
  congr 1
  funext axial
  rw [startupRawMatrix_value family _ axial closed,
    gluedCartesianFamilyField_same parameters lower positive bounded cofinal decreasing rows curves compatible index (point,axial) collar]
  have curve := (curves index).cartesianField_polar (bounded index) ‖point‖ (norm_pos_iff.mpr nonzero) angle axial
  rw [represented] at curve
  rw [curve]
  have matrix := operatorMatrix_action (coefficientPhysicalValue (family 0) axial closed)
    ((curves index).fullField (bounded index) (‖point‖,angle,axial))
  have diskSame : Grad.SourceCollarDivision.polarClosedPoint ‖point‖ angle
      ((positive index).le.trans collar.1) collar.2 = closed := by
    apply Subtype.ext
    simpa only [Grad.SourceCollarDivision.polarClosedPoint,closed,polarPlane_originalParametrization] using represented
  rw [diskSame]
  exact matrix.symm

/-- The existing native output moments represent the completed scaled
matrix product, before any Fourier cell is selected. -/
theorem nativeMatrix_scaledWeightedRep {output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 dimension output)
    (coherent : FamilyCoherent family) (scale : Scale) (field : StartupMoments output)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      field.field point cell = cartesianWeight parameters cell point •
        matrixFluxCell parameters family coherent lower positive bounded cofinal rows curves cell point) :
    StartupWeightedRep parameters.sigma0 parameters.gamma scale.val (field.dilate scale).field
      (fun pair => startupRawMatrix family
        (fun other => gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves (other.2,other.1))
        (pair.1,scale.val • pair.2)) := by
  have weighted := startupMomentDilation_weighted_same parameters.sigma0 parameters.gamma scale
    (matrixFluxCell parameters family coherent lower positive bounded cofinal rows curves) field.field same
  filter_upwards [weighted,startupDisk_ae_nonzero,ae_restrict_mem openUnitDisk_isOpen.measurableSet]
    with point actual nonzero inside
  intro cell
  have scaledNonzero : scale.val • point ≠ 0 := smul_ne_zero scale.property.1.ne' nonzero
  have scaledInside : ‖scale.val • point‖ < 1 := by
    rw [norm_smul,Real.norm_of_nonneg scale.property.1.le]
    exact (mul_le_of_le_one_left (norm_nonneg _) scale.property.2).trans_lt inside
  exact (actual cell).trans (congrArg (Grad.AnalyticWeights.Calculus.physicalWeight parameters.sigma0 parameters.gamma scale.val cell point • ·)
    (nativeMatrixCell_actual parameters lower positive bounded cofinal decreasing rows curves compatible family coherent cell
      (scale.val • point) scaledNonzero scaledInside))

end Grad.ActualScaledNativeCoefficients
