import AKDC6ConstructedOriginalSmoothBranch
import AXJ6ChartFlatJets
import AKAR15OriginalRotationProductRule
import AKBC22OriginalCoreCommutations
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3500
open Set
open scoped BigOperators
namespace Grad.OriginalZeroSeed
open Grad.CartesianState Grad.ClosedJets Grad.Constraints Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.PhysicalCoordinates Grad.Q24Realization Grad.RealFixedRanges Grad.ChartAxisProjections

variable {parameters : PhaseParameters}

theorem rootChart_zero_value (cell : ℝ) : coefficientValue (rootChart (0 : TangentCoefficient parameters)) cell = 1 := by
  have real : RealTangent (0 : TangentCoefficient parameters) := by
    intro index coordinate
    simp
  have axis : RootAxisCondition (0 : TangentCoefficient parameters) := by
    change tangentNorm 1 (0 : TangentCoefficient parameters) < (2 * axisConstant)⁻¹
    have zero : tangentNorm 1 (0 : TangentCoefficient parameters) = 0 := by simp [tangentNorm,tangentNormTerm]
    rw [zero]
    exact inv_pos.mpr (mul_pos (by norm_num) axisConstant_pos)
  rw [rootChart_value_eq_sqrt real axis]
  have value : planarValue (0 : TangentCoefficient parameters) cell = 0 := by
    simp [planarValue]
  rw [value]
  norm_num

theorem normalizedChart_zero (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) :
    normalizedChart parameters seed inside (0 : ChartState parameters) =
      (tameSeedField parameters seed inside,tameSeedScalar parameters seed inside) := by
  apply Prod.ext
  · change tameScalarMultiplier 3 (rootChart 0) (tameSeedField parameters seed inside)+
      valueMapCore parameters tameTangentInclusion
        (tameScalarMultiplier 1 (tangentComponent 0 0) (tameCoordinateScalarField parameters 0)+
          tameScalarMultiplier 1 (tangentComponent 0 1) (tameCoordinateScalarField parameters 1))+0 = _
    simp only [tangentComponent_zero,tameScalarMultiplier_zero_coefficient,add_zero,map_zero]
    apply coreValue_ext
    intro point cell
    rw [coreValue_tameScalarMultiplier,rootChart_zero_value,one_smul]
  · exact add_zero _

theorem physicalReferenceState_zero (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) :
    physicalReferenceState parameters reference insideR seed insideS (0 : JointState parameters) =
      (0,tameSeedField parameters seed insideS,tameSeedScalar parameters seed insideS) := by
  rw [physicalReferenceState_formula]
  change (0, normalizedChart parameters seed insideS (0,toPhysicalCore parameters (Gauges.seedTransfer parameters reference insideR seed insideS 0),0)) = _
  rw [map_zero,map_zero]
  exact congrArg (fun pair : ChartOutput parameters => ((0 : ℂ),pair)) (normalizedChart_zero seed insideS)

end Grad.OriginalZeroSeed
