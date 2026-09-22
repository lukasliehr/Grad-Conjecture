import AKDI2ActualSeedSpatialAlgebra
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3500
open Set Filter MeasureTheory
open scoped BigOperators
namespace Grad.OriginalZeroSeed
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.ChartAxisLift Grad.FinitePhysicalJetLift Grad.OriginalKernelRetainedDecay
open Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelHomogeneousGraph Grad.NonlinearProduct
open Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.Frame Grad.RawForward

variable {parameters : PhaseParameters}

theorem removeAngular_of_rotation_zero {dimension : ℕ} (field : ACore parameters dimension)
    (zero : rotationCore parameters field = 0) : removeAngularCore parameters field = 0 := by
  have mean : angularCore parameters 0 field = field := by
    apply coreValue_ext
    intro point axial
    have derivative (angle : ℝ) : HasDerivAt (fun time => coreValue field (rotatedPoint time point) axial) 0 angle := by
      simpa [zero,coreValue] using
        originalCoreOrbit_hasDerivAt parameters field point axial angle
    have values (angle : ℝ) : coreValue field (rotatedPoint angle point) axial = coreValue field point axial := by
      have equal := is_const_of_deriv_eq_zero (fun angle => (derivative angle).differentiableAt)
        (fun angle => (derivative angle).deriv) angle 0
      simpa only [rotatedPoint_zero] using equal
    rw [coreValue_angularCore]
    simp only [angularCharacter_zero_mode,one_smul,values]
    rw [intervalIntegral.integral_const,sub_zero,smul_smul,
      inv_mul_cancel₀ (by positivity : (2 * Real.pi) ≠ 0),one_smul]
  change field-angularCore parameters 0 field = 0
  rw [mean,sub_self]

variable (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)

theorem seedColumn_trace :
    dotOperation parameters (seedColumn seed inside 0) (seedColumn seed inside 0) +
      dotOperation parameters (seedColumn seed inside 1) (seedColumn seed inside 1) =
      (2 : ℂ) • scalarConstantCore parameters 1 := by
  apply coreValue_ext
  intro point axial
  apply PiLp.ext
  intro coordinate
  obtain rfl := Fin.eq_zero coordinate
  rw [coreValue_add,coreValue_smul]
  change coreValue (dotOperation parameters (seedColumn seed inside 0) (seedColumn seed inside 0)) point axial 0 +
    coreValue (dotOperation parameters (seedColumn seed inside 1) (seedColumn seed inside 1)) point axial 0 = _
  rw [coreValue_dotOperation,coreValue_dotOperation]
  simp only [seedColumn,coreValue_valueMap,coreValue_seedMatrix,coreValue_constant,scalarConstantCore]
  have trace := Gauges.seedMatrix_trace_pointwise seed inside axial
  rw [Gauges.transposeOperator_comp_trace] at trace
  have basis (direction : Fin 2) : Gauges.planarBasis direction = (EuclideanSpace.single direction 1 : ComplexEuclidean 2) := by
    apply PiLp.ext
    intro coordinate
    fin_cases direction <;> fin_cases coordinate <;> rfl
  simp only [Gauges.operatorEntry,basis] at trace
  simpa [Grad.NonlinearQuotient.complexDot,Fin.sum_univ_three,tamePlanarInclusion,pow_two,add_assoc] using trace

theorem actualSeed_energySum :
    dotOperation parameters (tameSeedField parameters seed inside) (tameSeedField parameters seed inside) +
      dotOperation parameters (rotationCore parameters (tameSeedField parameters seed inside))
        (rotationCore parameters (tameSeedField parameters seed inside)) =
      (2 : ℂ) • radiusSquaredCore parameters (scalarConstantCore parameters 1) := by
  have expanded : dotOperation parameters (tameSeedField parameters seed inside) (tameSeedField parameters seed inside) +
      dotOperation parameters (rotationCore parameters (tameSeedField parameters seed inside))
        (rotationCore parameters (tameSeedField parameters seed inside)) =
      radiusSquaredCore parameters (dotOperation parameters (seedColumn seed inside 0) (seedColumn seed inside 0) +
        dotOperation parameters (seedColumn seed inside 1) (seedColumn seed inside 1)) := by
    rw [actualSeed_rotation,actualSeed_decomposition,radiusSquaredCore_coordinates]
    simp only [map_add,LinearMap.add_apply,map_sub,LinearMap.sub_apply,dot_coordinate_first,dot_coordinate_second,
      coordinateCore_commute 1 0]
    abel
  rw [expanded,seedColumn_trace,map_smul]

theorem actualSeed_firstRaw :
    rotationCore parameters (tameSeedScalar parameters seed inside) -
      dotOperation parameters (rotationCore parameters (tameSeedField parameters seed inside))
        (rotationCore parameters (tameSeedField parameters seed inside)) +
      radiusSquaredCore parameters (scalarConstantCore parameters 1) = 0 := by
  rw [actualSeedScalar_dot,map_smul,originalDot_rotation,actualSeed_rotation_twice]
  simp only [map_neg]
  have radius : radiusSquaredCore parameters (scalarConstantCore parameters 1) =
      (1/2 : ℂ) • (dotOperation parameters (tameSeedField parameters seed inside) (tameSeedField parameters seed inside) +
        dotOperation parameters (rotationCore parameters (tameSeedField parameters seed inside))
          (rotationCore parameters (tameSeedField parameters seed inside))) := by
    rw [actualSeed_energySum,smul_smul]
    norm_num
  rw [radius]
  module

theorem actualSeed_secondRaw :
    removeAngularCore parameters (eulerCore parameters (tameSeedScalar parameters seed inside) -
      dotOperation parameters (eulerCore parameters (tameSeedField parameters seed inside))
        (rotationCore parameters (tameSeedField parameters seed inside))) = 0 := by
  rw [actualSeedScalar_euler,actualSeed_euler,sub_self,map_zero]

end Grad.OriginalZeroSeed
