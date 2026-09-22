import AKDI4SeedThirdRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3500
namespace Grad.OriginalZeroSeed
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.FinitePhysicalJetLift Grad.OriginalKernelRetainedDecay Grad.OriginalKernelCovariantRecovery
open Grad.OriginalKernelHomogeneousGraph Grad.RawForward

variable {parameters : PhaseParameters}

theorem zeroSeed_determinant_rotation (first second third : ACore parameters 3) :
    rotationCore parameters (determinantOperation parameters first second third) =
      determinantOperation parameters (rotationCore parameters first) second third +
        determinantOperation parameters first (rotationCore parameters second) third +
        determinantOperation parameters first second (rotationCore parameters third) := by
  let : AddCommGroup (ACore parameters 1) := inferInstance
  let : Module ℂ (ACore parameters 1) := inferInstance
  let : AddCommGroup (ACore parameters 3 →ₗ[ℂ] ACore parameters 1) := inferInstance
  let : Module ℂ (ACore parameters 3 →ₗ[ℂ] ACore parameters 1) := inferInstance
  let : AddCommGroup (ACore parameters 3 →ₗ[ℂ] ACore parameters 3 →ₗ[ℂ] ACore parameters 1) := inferInstance
  have firstSlot : determinantOperation parameters (rotationCore parameters first) second third =
      coordinateCore parameters 0 (determinantOperation parameters (partialCore parameters 1 first) second third) -
        coordinateCore parameters 1 (determinantOperation parameters (partialCore parameters 0 first) second third) := by
    change determinantOperation parameters
      (coordinateCore parameters 0 (partialCore parameters 1 first) - coordinateCore parameters 1 (partialCore parameters 0 first)) second third = _
    rw [map_sub,LinearMap.sub_apply,LinearMap.sub_apply,determinant_coordinate_first,determinant_coordinate_first]
  have secondSlot : determinantOperation parameters first (rotationCore parameters second) third =
      coordinateCore parameters 0 (determinantOperation parameters first (partialCore parameters 1 second) third) -
        coordinateCore parameters 1 (determinantOperation parameters first (partialCore parameters 0 second) third) := by
    change determinantOperation parameters first
      (coordinateCore parameters 0 (partialCore parameters 1 second) - coordinateCore parameters 1 (partialCore parameters 0 second)) third = _
    rw [map_sub,LinearMap.sub_apply,determinant_coordinate_second,determinant_coordinate_second]
  have thirdSlot : determinantOperation parameters first second (rotationCore parameters third) =
      coordinateCore parameters 0 (determinantOperation parameters first second (partialCore parameters 1 third)) -
        coordinateCore parameters 1 (determinantOperation parameters first second (partialCore parameters 0 third)) := by
    change determinantOperation parameters first second
      (coordinateCore parameters 0 (partialCore parameters 1 third) - coordinateCore parameters 1 (partialCore parameters 0 third)) = _
    rw [map_sub,determinant_coordinate_third,determinant_coordinate_third]
  rw [firstSlot,secondSlot,thirdSlot]
  change coordinateCore parameters 0 (partialCore parameters 1 (determinantOperation parameters first second third)) -
    coordinateCore parameters 1 (partialCore parameters 0 (determinantOperation parameters first second third)) = _
  rw [originalDeterminant_partial,originalDeterminant_partial]
  simp only [map_add]
  abel

variable (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)

theorem actualSeed_fourthRaw (length : ℝ) :
    removeAngularCore parameters (determinantOperation parameters (eulerCore parameters (tameSeedField parameters seed inside))
      (rotationCore parameters (tameSeedField parameters seed inside))
      (affineStateCore parameters length (0,tameSeedField parameters seed inside,tameSeedScalar parameters seed inside))) = 0 := by
  rw [actualSeed_euler]
  apply removeAngular_of_rotation_zero
  rw [zeroSeed_determinant_rotation,actualSeed_rotation_twice,originalRotation_affine]
  simp only [map_neg,LinearMap.neg_apply,determinantOperation_self,neg_zero,zero_add,
    physicalVariationAffine,zero_smul,add_zero]
  rw [tameSeedField,originalRotation_valueMap,zeroSeed_time_valueMap,includedPlanar_determinant]

theorem actualSeed_rawRows (length : ℝ) :
    originalRawRowsCore parameters length
      (0,tameSeedField parameters seed inside,tameSeedScalar parameters seed inside) = 0 := by
  funext row
  fin_cases row
  · exact actualSeed_firstRaw seed inside
  · exact actualSeed_secondRaw seed inside
  · exact actualSeed_thirdRaw seed inside length
  · exact actualSeed_fourthRaw seed inside length

end Grad.OriginalZeroSeed
