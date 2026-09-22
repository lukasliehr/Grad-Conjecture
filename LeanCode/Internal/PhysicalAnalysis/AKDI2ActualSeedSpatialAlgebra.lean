import AKDI1OriginalZeroChart
import AKAR23ActualTotalFrameRotation
import AKBI5ActualHomogeneousXiEuler
import AXL13SeedToroidal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3500
open scoped BigOperators
namespace Grad.OriginalZeroSeed
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.ChartAxisLift Grad.FinitePhysicalJetLift Grad.OriginalKernelRetainedDecay
open Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelHomogeneousGraph Grad.NonlinearProduct

variable {parameters : PhaseParameters} (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)

def seedColumn (direction : Fin 2) : ACore parameters 3 :=
  valueMapCore parameters tamePlanarInclusion (Gauges.seedMatrixCore parameters seed inside
    (constantCore parameters (EuclideanSpace.single direction 1)))

theorem seedColumn_partial (direction coordinate : Fin 2) :
    partialCore parameters coordinate (seedColumn seed inside direction) = 0 := by
  rw [seedColumn,partialCore_valueMap,partialCore_seedMatrix,originalConstant_partial,map_zero,map_zero]

theorem actualSeed_decomposition : tameSeedField parameters seed inside =
    coordinateCore parameters 0 (seedColumn seed inside 0) +
      coordinateCore parameters 1 (seedColumn seed inside 1) := by
  apply coreValue_ext
  intro point axial
  rw [tameSeedField,coreValue_valueMap,tameSeedPlanarField,coreValue_seedMatrix,coreValue_planarCoordinate,
    coreValue_add,coreValue_coordinate,coreValue_coordinate]
  simp only [seedColumn,coreValue_valueMap,coreValue_seedMatrix,coreValue_constant]
  simp only [← Complex.coe_smul]
  have pointSame : complexDiskPoint point = (point.val 0 : ℂ) • EuclideanSpace.single 0 1 +
      (point.val 1 : ℂ) • EuclideanSpace.single 1 1 := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [complexDiskPoint]
  simp only [pointSame,map_add,map_smul]

theorem actualSeed_partial (direction : Fin 2) :
    partialCore parameters direction (tameSeedField parameters seed inside) = seedColumn seed inside direction := by
  rw [actualSeed_decomposition,map_add,partialCore_coordinateCore,partialCore_coordinateCore,
    seedColumn_partial,seedColumn_partial,map_zero,map_zero,add_zero,add_zero]
  fin_cases direction <;> simp

theorem actualSeed_euler : eulerCore parameters (tameSeedField parameters seed inside) =
    tameSeedField parameters seed inside := by
  change coordinateCore parameters 0 (partialCore parameters 0 (tameSeedField parameters seed inside)) +
    coordinateCore parameters 1 (partialCore parameters 1 (tameSeedField parameters seed inside)) = _
  rw [actualSeed_partial,actualSeed_partial]
  exact (actualSeed_decomposition seed inside).symm

theorem actualSeed_rotation : rotationCore parameters (tameSeedField parameters seed inside) =
    coordinateCore parameters 0 (seedColumn seed inside 1) -
      coordinateCore parameters 1 (seedColumn seed inside 0) := by
  change coordinateCore parameters 0 (partialCore parameters 1 (tameSeedField parameters seed inside)) -
    coordinateCore parameters 1 (partialCore parameters 0 (tameSeedField parameters seed inside)) = _
  rw [actualSeed_partial,actualSeed_partial]

theorem actualSeed_rotation_twice : rotationCore parameters (rotationCore parameters (tameSeedField parameters seed inside)) =
    -tameSeedField parameters seed inside := by
  rw [actualSeed_rotation,actualSeed_decomposition]
  simp [rotationCore,partialCore_coordinateCore,seedColumn_partial,map_sub]
  abel

theorem actualRadius_rotation : rotationCore parameters (tameRadiusSquareField parameters) = 0 := by
  simp only [tameRadiusSquareField,tameCoordinateScalarField,singleton_coordinate]
  change rotationCore parameters (coordinateCore parameters 0 (coordinateCore parameters 0
    (constantCore parameters (EuclideanSpace.single 0 1))) + coordinateCore parameters 1
    (coordinateCore parameters 1 (constantCore parameters (EuclideanSpace.single 0 1)))) = 0
  simp [rotationCore,partialCore_coordinateCore,originalConstant_partial,map_add,
    coordinateCore_commute 1 0]

theorem actualSeedScalar_dot : tameSeedScalar parameters seed inside =
    (1/2 : ℂ) • dotOperation parameters (tameSeedField parameters seed inside)
      (rotationCore parameters (tameSeedField parameters seed inside)) := by
  have energy : tameSeedEnergy parameters seed inside =
      dotOperation parameters (rotationCore parameters (tameSeedField parameters seed inside))
        (rotationCore parameters (tameSeedField parameters seed inside)) - tameRadiusSquareField parameters := by
    rw [tameSeedEnergy,dotOperation,pairProductLinear_apply]
  rw [tameSeedScalar,energy,map_sub,originalDot_rotation,actualSeed_rotation_twice,actualRadius_rotation,sub_zero]
  simp only [map_neg,LinearMap.neg_apply]
  rw [originalDot_comm (rotationCore parameters (tameSeedField parameters seed inside))]
  module

theorem actualSeedScalar_euler : eulerCore parameters (tameSeedScalar parameters seed inside) =
    dotOperation parameters (tameSeedField parameters seed inside)
      (rotationCore parameters (tameSeedField parameters seed inside)) := by
  rw [actualSeedScalar_dot,map_smul,originalDot_euler,originalEuler_rotation,actualSeed_euler]
  module

end Grad.OriginalZeroSeed
