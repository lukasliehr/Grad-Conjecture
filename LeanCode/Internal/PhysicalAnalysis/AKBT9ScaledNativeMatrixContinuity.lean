import AKBT8WeightedNativeRepresentationAlgebra
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
/-- Full native matrix products remain continuous on every punctured
scaled angular circle, which justifies the literal Fourier selection. -/
theorem nativeScaledMatrix_axial_continuous {output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 dimension output)
    (scale : Scale) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, Continuous (fun angle => startupRawMatrix family
      (fun other => gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves (other.2,other.1))
      (angle,scale.val • point)) := by
  have original : ContinuousOn
      (fun other : ℝ × Spatial => gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves (other.2,other.1))
      {pair | pair.2 ∈ openUnitDisk \ {(0 : Spatial)}} := by
    have unit := scaledNativeFamilyRaw_punctured_continuous parameters lower positive bounded cofinal decreasing rows curves compatible 1 zero_lt_one le_rfl
    change ContinuousOn (fun other : ℝ × Spatial => gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves (1 • other.2,other.1)) _ at unit
    simpa only [one_smul] using unit
  have product := startupRawMatrix_punctured_continuous (unitDiskAdmissible parameters) family _ original
  filter_upwards [startupDisk_ae_nonzero,ae_restrict_mem openUnitDisk_isOpen.measurableSet]
    with point nonzero inside
  have scaledNonzero : scale.val • point ≠ 0 := smul_ne_zero scale.property.1.ne' nonzero
  have scaledInside : ‖scale.val • point‖ < 1 := by
    rw [norm_smul,Real.norm_of_nonneg scale.property.1.le]
    exact (mul_le_of_le_one_left (norm_nonneg _) scale.property.2).trans_lt inside
  exact product.comp_continuous (by fun_prop) (fun _ => ⟨scaledInside,by simpa only [mem_singleton_iff] using scaledNonzero⟩)

end Grad.ActualScaledNativeCoefficients
