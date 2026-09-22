import QO14PhysicalProduct
import QO15ChartFirstJet

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 800000

open scoped ComplexConjugate BigOperators

namespace Grad.NonlinearRange

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.AxisSplit Grad.GaugeCoefficients.Physical.Frame
open Grad.QuotientProjection

variable {parameters : PhaseParameters}

theorem partialCore_tameScalarMultiplier {dimension : ℕ} [Nontrivial (ComplexEuclidean dimension)]
    (family : TameCoefficient parameters) (direction : Fin 2) (field : ACore parameters dimension) :
    partialCore parameters direction (tameScalarMultiplier dimension family field) =
      tameScalarMultiplier dimension family (partialCore parameters direction field) :=
  partialCore_smoothMultiplier _ _ direction field

theorem normalizedChart_firstJet (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (state : ChartState parameters) (zeroJets : ∀ cell, ZeroCartesianFirstJets (state.2.1.val cell))
    (direction : Fin 2) (angle : ℝ) :
    coreValue (partialCore parameters direction (normalizedChart parameters seed inside state).1) originPoint angle =
      coefficientValue (rootChart state.1) angle •
        tamePlanarInclusion (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3) angle
          (EuclideanSpace.single direction 1)) +
      tameTangentInclusion (planarValue state.1 angle direction • EuclideanSpace.single 0 1) := by
  change coreValue (partialCore parameters direction
    (tameScalarMultiplier 3 (rootChart state.1) (tameSeedField parameters seed inside) +
      valueMapCore parameters tameTangentInclusion
        (tameScalarMultiplier 1 (tangentComponent state.1 0) (tameCoordinateScalarField parameters 0) +
          tameScalarMultiplier 1 (tangentComponent state.1 1) (tameCoordinateScalarField parameters 1)) +
      state.2.1)) originPoint angle = _
  rw [map_add, map_add, coreValue_add, coreValue_add,
    partialCore_tameScalarMultiplier, coreValue_tameScalarMultiplier, axisDerivative_tameSeedField,
    partialCore_valueMap, coreValue_valueMap, map_add, coreValue_add,
    partialCore_tameScalarMultiplier, partialCore_tameScalarMultiplier,
    coreValue_tameScalarMultiplier, coreValue_tameScalarMultiplier,
    axisDerivative_tameCoordinate, axisDerivative_tameCoordinate,
    axisDerivative_zeroJets _ zeroJets, add_zero]
  fin_cases direction <;> norm_num [planarValue_apply]

theorem normalizedColumn_dot (scalar : ℂ) (vector : ComplexEuclidean 2) (tangent : ℂ) :
    Grad.NonlinearQuotient.complexDot
      (scalar • tamePlanarInclusion vector + tameTangentInclusion (tangent • EuclideanSpace.single 0 1))
      (scalar • tamePlanarInclusion vector + tameTangentInclusion (tangent • EuclideanSpace.single 0 1)) =
      scalar ^ 2 * (vector 0 ^ 2 + vector 1 ^ 2) + tangent ^ 2 := by
  unfold Grad.NonlinearQuotient.complexDot
  rw [Fin.sum_univ_three]
  change (scalar * vector 0 + 0) * (scalar * vector 0 + 0) +
    (scalar * 0 + tangent * 1) * (scalar * 0 + tangent * 1) +
    (scalar * vector 1 + 0) * (scalar * vector 1 + 0) = _
  ring

theorem normalizedColumns_square (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (scalar : ℂ) (tangent : ComplexEuclidean 2)
    (traceTwo : Gauges.operatorEntry mapping 0 0 ^ 2 + Gauges.operatorEntry mapping 1 0 ^ 2 +
      Gauges.operatorEntry mapping 0 1 ^ 2 + Gauges.operatorEntry mapping 1 1 ^ 2 = 2) :
    Grad.NonlinearQuotient.complexDot
        (scalar • tamePlanarInclusion (mapping (EuclideanSpace.single 0 1)) +
          tameTangentInclusion (tangent 0 • EuclideanSpace.single 0 1))
        (scalar • tamePlanarInclusion (mapping (EuclideanSpace.single 0 1)) +
          tameTangentInclusion (tangent 0 • EuclideanSpace.single 0 1)) +
      Grad.NonlinearQuotient.complexDot
        (scalar • tamePlanarInclusion (mapping (EuclideanSpace.single 1 1)) +
          tameTangentInclusion (tangent 1 • EuclideanSpace.single 0 1))
        (scalar • tamePlanarInclusion (mapping (EuclideanSpace.single 1 1)) +
          tameTangentInclusion (tangent 1 • EuclideanSpace.single 0 1)) =
      2 * scalar ^ 2 + tangent 0 ^ 2 + tangent 1 ^ 2 := by
  rw [normalizedColumn_dot, normalizedColumn_dot]
  change scalar ^ 2 * (Gauges.operatorEntry mapping 0 0 ^ 2 + Gauges.operatorEntry mapping 1 0 ^ 2) +
    tangent 0 ^ 2 + (scalar ^ 2 * (Gauges.operatorEntry mapping 0 1 ^ 2 +
      Gauges.operatorEntry mapping 1 1 ^ 2) + tangent 1 ^ 2) = _
  calc
    _ = scalar ^ 2 * (Gauges.operatorEntry mapping 0 0 ^ 2 + Gauges.operatorEntry mapping 1 0 ^ 2 +
        Gauges.operatorEntry mapping 0 1 ^ 2 + Gauges.operatorEntry mapping 1 1 ^ 2) +
        tangent 0 ^ 2 + tangent 1 ^ 2 := by ring
    _ = _ := by rw [traceTwo]; ring

theorem normalizedChart_traceTwo (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (state : ChartState parameters) (zeroJets : ∀ cell, ZeroCartesianFirstJets (state.2.1.val cell))
    (real : RealTangent state.1) (axis : ChartAxisCondition state) (angle : ℝ) :
    coreValue (dotOperation parameters
        (partialCore parameters 0 (normalizedChart parameters seed inside state).1)
        (partialCore parameters 0 (normalizedChart parameters seed inside state).1) +
      dotOperation parameters
        (partialCore parameters 1 (normalizedChart parameters seed inside state).1)
        (partialCore parameters 1 (normalizedChart parameters seed inside state).1)) originPoint angle =
      EuclideanSpace.single 0 2 := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  change coreValue (dotOperation parameters
        (partialCore parameters 0 (normalizedChart parameters seed inside state).1)
        (partialCore parameters 0 (normalizedChart parameters seed inside state).1) +
      dotOperation parameters
        (partialCore parameters 1 (normalizedChart parameters seed inside state).1)
        (partialCore parameters 1 (normalizedChart parameters seed inside state).1)) originPoint angle 0 = 2
  rw [coreValue_add, PiLp.add_apply, coreValue_dotOperation, coreValue_dotOperation,
    normalizedChart_firstJet seed inside state zeroJets, normalizedChart_firstJet seed inside state zeroJets]
  have traceTwo := Gauges.seedMatrix_trace_pointwise seed inside angle
  rw [Gauges.transposeOperator_comp_trace] at traceTwo
  rw [normalizedColumns_square _ _ _ traceTwo]
  have rootIdentity := congrArg (fun coefficient : TameCoefficient parameters => coefficientValue coefficient angle)
    (rootChart_square state.1 real axis)
  rw [coefficientValue_add, coefficientValue_pow, coefficientValue_one,
    coefficientValue_tangentQuadratic] at rootIdentity
  linear_combination (2 : ℂ) * rootIdentity

end Grad.NonlinearRange
