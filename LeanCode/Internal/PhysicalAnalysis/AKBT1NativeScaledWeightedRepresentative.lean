import AKBQ10ActualScaledNativeGaugeFamily
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
/-- The native joint weighted field represents the SAME entire scaled
physical Fourier family, with the original phase and every axial cell. -/
theorem nativeFamily_scaledWeightedRep (scale : Scale) (field : StartupMoments dimension)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      field.field point cell = cartesianWeight parameters cell point •
        gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell point) :
    StartupWeightedRep parameters.sigma0 parameters.gamma scale.val (field.dilate scale).field
      (scaledNativeFamilyRaw parameters lower positive bounded cofinal rows curves scale.val) := by
  have weighted := startupMomentDilation_weighted_same parameters.sigma0 parameters.gamma scale
    (gluedCartesianCellField parameters lower positive bounded cofinal rows curves) field.field same
  filter_upwards [weighted,startupDisk_ae_nonzero,ae_restrict_mem openUnitDisk_isOpen.measurableSet]
    with point actual nonzero inside
  intro cell
  have scaledNonzero : scale.val • point ≠ 0 := smul_ne_zero scale.property.1.ne' nonzero
  have scaledInside : ‖scale.val • point‖ < 1 := by
    rw [norm_smul,Real.norm_of_nonneg scale.property.1.le]
    exact (mul_le_of_le_one_left (norm_nonneg _) scale.property.2).trans_lt inside
  exact (actual cell).trans (congrArg (Grad.AnalyticWeights.Calculus.physicalWeight parameters.sigma0 parameters.gamma scale.val cell point • ·)
    (nativeFamilyCell_actual parameters lower positive bounded cofinal decreasing rows curves compatible cell (scale.val • point) scaledNonzero scaledInside))

end Grad.ActualScaledNativeCoefficients
