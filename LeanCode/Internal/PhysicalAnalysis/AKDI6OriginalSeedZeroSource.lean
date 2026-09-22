import AKDI5SeedFourthRow
import AXI5RawReconstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3500
namespace Grad.OriginalZeroSeed
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.RawForward Grad.RawSourceFaithfulness Grad.QuotientProjection
open Grad.SmoothingFamily
open Grad.PhysicalCoordinates Grad.Q24Realization Grad.RealFixedRanges Grad.NashMoser.OriginalLimit

variable {parameters : PhaseParameters}

theorem actualSeed_quotientRows_zero (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) (length : ℝ) :
    quotientPolynomialRows parameters length
      (0,tameSeedField parameters seed inside,tameSeedScalar parameters seed inside) = 0 := by
  have gauge : GaugeState parameters
      (0,tameSeedField parameters seed inside,tameSeedScalar parameters seed inside) :=
    tameSeedScalar_mean_zero seed inside
  apply quotientEta_injective parameters 0
  apply rawReconstructionCompleted_injective parameters
  rw [rawReconstructionCompleted_core,rawReconstructionCompleted_core,
    rawReconstruction_polynomial length _ gauge,actualSeed_rawRows]
  simp only [map_zero]

theorem physicalFixedSliceMap_seed_zero (length : ℝ) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) :
    physicalFixedSliceMap parameters length reference insideR seed insideS (0 : JointState parameters) = 0 := by
  rw [physicalFixedSliceMap,physicalReferenceState_zero,actualSeed_quotientRows_zero]

theorem zeroChart_axis : ChartAxisCondition (0 : ChartState parameters) := by
  change tangentNorm 1 (0 : TangentCoefficient parameters) < (2*axisConstant)⁻¹
  have zero : tangentNorm 1 (0 : TangentCoefficient parameters) = 0 := by simp [tangentNorm,tangentNormTerm]
  rw [zero]
  exact inv_pos.mpr (mul_pos (by norm_num) axisConstant_pos)

theorem smoothingChartCore_zero : smoothingChartCore parameters (0 : StateCore parameters) = 0 := by
  change (smoothingToTangent parameters 0, (0,0)) = (0,0,0)
  rw [map_zero]

/-- Every admissible original seed has literal zero nonlinear source at zero
curvature and zero constrained state, at the original analytic width. -/
theorem originalNonlinearSource_seed_zero (length : ℝ) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) :
    originalNonlinearSource parameters length reference insideR (seed,0)
      (0 : stateSmoothRange parameters reference insideR) = 0 := by
  have axis : ChartAxisCondition (smoothingChartCore parameters
      (0 : stateSmoothRange parameters reference insideR).val) := by
    change ChartAxisCondition (smoothingChartCore parameters (0 : StateCore parameters))
    rw [smoothingChartCore_zero]
    exact zeroChart_axis
  apply Subtype.ext
  rw [originalNonlinearSource_value parameters length reference insideR (seed,0) 0 insideS axis]
  change physicalFixedSliceMap parameters length reference insideR seed insideS
    (((0 : ℝ) : ℂ), smoothingChartCore parameters (0 : StateCore parameters)) = 0
  rw [Complex.ofReal_zero,smoothingChartCore_zero]
  exact physicalFixedSliceMap_seed_zero length reference insideR seed insideS

end Grad.OriginalZeroSeed
