import AKDP19SameOriginalRankLinear
import AKDR5OriginalEquivariantAverageNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.NonlinearProduct Grad.Constraints.Gauges Grad.GaugeCoefficients.Radial
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.Constraints
open Grad.OriginalCoreRealization Grad.ActualOriginalSourceMoments Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope

/-- The actual point action on the original core, including reflection. -/
def startupOriginalPointCore {input output : ℕ} (parameters : PhaseParameters)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (core : ACore parameters input) : ACore parameters output :=
  valueMapCore parameters mapping (orthogonalCore parameters orthogonal core)

theorem startupOriginalPointCore_bound {input output : ℕ} (parameters : PhaseParameters)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (core : ACore parameters input) (grade : ℕ) :
    originalGradeNorm grade (startupOriginalPointCore parameters mapping orthogonal core) ≤
      (‖mapping‖*orthogonalGradeConstant grade)*originalGradeNorm grade core := by
  have orthogonalBound : originalGradeNorm grade (orthogonalCore parameters orthogonal core) ≤
      orthogonalGradeConstant grade*originalGradeNorm grade core := by
    unfold originalGradeNorm
    rw [ofCoreLinear_norm_coordinates,ofCoreLinear_norm_coordinates]
    exact orthogonalCore_coordinates_bound parameters orthogonal core grade
  exact (valueMapCore_bound mapping _ grade).trans
    ((mul_le_mul_of_nonneg_left orthogonalBound (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm)

theorem startupOriginalPointCore_sameField {input output : ℕ} (parameters : PhaseParameters)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (core : ACore parameters input) :
    originalSourceFieldLinear parameters (startupOriginalPointCore parameters mapping orthogonal core) =
      startupPointKernel mapping orthogonal (originalSourceFieldLinear parameters core) := by
  apply startupField_ae_ext
  have moved := (startupOrthogonal_disk_preserving orthogonal).quasiMeasurePreserving.ae
    (originalSource_field_closed parameters core)
  filter_upwards [originalSource_field_closed parameters (startupOriginalPointCore parameters mapping orthogonal core),
    moved,startupPointKernel_field_ae mapping orthogonal (originalSourceFieldLinear parameters core),
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point image original action inside
  intro cell
  change (originalSourceMoments parameters (startupOriginalPointCore parameters mapping orthogonal core)).field point cell = _
  rw [image cell,action cell]
  change _ = mapping ((originalSourceMoments parameters core).field (orthogonal point) cell)
  rw [original cell]
  have closed := openDiskMembershipClosed point inside
  have rotatedClosed : orthogonal point ∈ closedUnitDisk := by
    change ‖orthogonal point‖ ≤ 1
    rw [orthogonal.norm_map]
    exact closed
  simp only [closedDiskLift,dif_pos closed,dif_pos rotatedClosed,phaseWeightedJet_value,
    startupOriginalPointCore,valueMapCore_value,orthogonalCore_apply]
  change cartesianWeight parameters cell point • mapping ((core.val cell).value
    (orthogonalClosedPoint orthogonal ⟨point,closed⟩)) =
    mapping (cartesianWeight parameters cell (orthogonal point) • (core.val cell).value _)
  have weightSame : cartesianWeight parameters cell (orthogonal point) = cartesianWeight parameters cell point := by
    change originalWeight parameters.sigma0 parameters.gamma 1 cell (orthogonal point) = _
    exact apWeight_orthogonal parameters.sigma0 parameters.gamma 1 cell orthogonal point
  rw [weightSame,mapping.map_smul_of_tower]
  rfl

end Grad.CartesianStartup
