import AKDI3SeedFirstRows
import AKBI14OriginalDeterminantProductDifferentiation
import AKBC23OriginalHomogeneousThirdIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3500
open scoped BigOperators
namespace Grad.OriginalZeroSeed
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.ChartAxisLift Grad.FinitePhysicalJetLift Grad.OriginalKernelRetainedDecay
open Grad.AxisSplit
open Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelHomogeneousGraph Grad.NonlinearProduct Grad.RawForward

variable {parameters : PhaseParameters}

theorem zeroSeed_time_valueMap {input output : ℕ} (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (field : ACore parameters input) :
    timeDerivativeCore parameters (valueMapCore parameters mapping field) =
      valueMapCore parameters mapping (timeDerivativeCore parameters field) := by
  apply Subtype.ext
  funext cell
  rw [timeDerivativeCore_val,valueMapCore_val,valueMapCore_val,timeDerivativeCore_val]
  exact ((valueMapJetLinear input output mapping).map_smul ((cell : ℂ)*Complex.I) (field.val cell)).symm

theorem includedPlanar_tangentDot (field : ACore parameters 2) :
    dotOperation parameters (valueMapCore parameters tamePlanarInclusion field) (eTConstantCore parameters) = 0 := by
  apply coreValue_ext
  intro point axial
  apply PiLp.ext
  intro coordinate
  obtain rfl := Fin.eq_zero coordinate
  rw [coreValue_dotOperation,coreValue_valueMap,eTConstantCore,coreValue_constant]
  simp [Grad.NonlinearQuotient.complexDot,tamePlanarInclusion,coreValue]

theorem includedPlanar_determinant (first second third : ACore parameters 2) :
    determinantOperation parameters (valueMapCore parameters tamePlanarInclusion first)
      (valueMapCore parameters tamePlanarInclusion second) (valueMapCore parameters tamePlanarInclusion third) = 0 := by
  apply coreValue_ext
  intro point axial
  apply PiLp.ext
  intro coordinate
  obtain rfl := Fin.eq_zero coordinate
  rw [coreValue_determinantOperation,coreValue_valueMap,coreValue_valueMap,coreValue_valueMap]
  simp [Grad.NonlinearQuotient.complexDeterminant_eq,tamePlanarInclusion,coreValue]

variable (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)

theorem actualSeed_thirdRaw (length : ℝ) :
    removeAngularCore parameters (dotOperation parameters (rotationCore parameters (tameSeedField parameters seed inside))
      (affineStateCore parameters length (0,tameSeedField parameters seed inside,tameSeedScalar parameters seed inside)) -
      timeDerivativeCore parameters (tameSeedScalar parameters seed inside)) = 0 := by
  have affine : dotOperation parameters (rotationCore parameters (tameSeedField parameters seed inside))
      (affineStateCore parameters length (0,tameSeedField parameters seed inside,tameSeedScalar parameters seed inside)) =
      dotOperation parameters (rotationCore parameters (tameSeedField parameters seed inside))
        (timeDerivativeCore parameters (tameSeedField parameters seed inside)) := by
    simp only [affineStateCore,stateField_apply,stateScalar_apply,zero_smul,add_zero,map_add,map_smul]
    have tangent : dotOperation parameters (rotationCore parameters (tameSeedField parameters seed inside))
        (eTConstantCore parameters) = 0 := by
      rw [tameSeedField,originalRotation_valueMap,includedPlanar_tangentDot]
    rw [tangent,smul_zero,add_zero]
  rw [affine]
  apply removeAngular_of_rotation_zero
  rw [actualSeedScalar_dot]
  simp only [map_sub,map_smul,map_add,originalDot_rotation,originalDot_time,← originalTime_rotation,
    actualSeed_rotation_twice,map_neg,LinearMap.neg_apply]
  rw [originalDot_comm (timeDerivativeCore parameters (tameSeedField parameters seed inside)),
    originalDot_comm (timeDerivativeCore parameters (rotationCore parameters (tameSeedField parameters seed inside)))]
  module

end Grad.OriginalZeroSeed
