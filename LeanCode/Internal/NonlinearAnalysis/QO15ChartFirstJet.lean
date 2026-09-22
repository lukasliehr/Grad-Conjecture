import QO13PhysicalValues
import TameChartInterface

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Grad.NonlinearRange

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.AxisSplit Grad.GaugeCoefficients.Physical.Frame

variable {parameters : PhaseParameters}

theorem partialCore_smoothMultiplier {inputDimension outputDimension : ℕ}
    (coefficients : ℤ → ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension)
    (summable : ∀ grade, Summable (Multipliers.envelopeTerm parameters grade coefficients))
    (direction : Fin 2) (field : ACore parameters inputDimension) :
    partialCore parameters direction (Gauges.smoothMultiplier parameters coefficients summable field) =
      Gauges.smoothMultiplier parameters coefficients summable (partialCore parameters direction field) := by
  apply acore_ext
  intro cell point
  exact (Gauges.smoothMultiplier_derivative_hasSum parameters coefficients summable field cell 1
    (fun _ => direction) point).unique
      (Gauges.smoothMultiplier_value_hasSum parameters coefficients summable
        (partialCore parameters direction field) cell point)

theorem partialCore_valueMap {inputDimension outputDimension : ℕ}
    (mapping : ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension)
    (direction : Fin 2) (field : ACore parameters inputDimension) :
    partialCore parameters direction (valueMapCore parameters mapping field) =
      valueMapCore parameters mapping (partialCore parameters direction field) := by
  apply acore_ext
  intro cell point
  change closedDerivative (valueMapJet mapping (field.val cell)) 1 (fun _ => direction) point = _
  rw [valueMapJet_derivative]
  rw [valueMapCore_value]
  rfl

theorem coreValue_tameScalarMultiplier {dimension : ℕ} [Nontrivial (ComplexEuclidean dimension)]
    (family : TameCoefficient parameters) (field : ACore parameters dimension)
    (point : ClosedDisk) (angle : ℝ) :
    coreValue (tameScalarMultiplier dimension family field) point angle =
      coefficientValue family angle • coreValue field point angle := by
  rw [tameScalarMultiplier, coreValue_smoothMultiplier]
  have operators : (∑' cell, axialPhase cell angle • tameScalarOperator dimension family.val cell) =
      coefficientValue family angle • ContinuousLinearMap.id ℂ (ComplexEuclidean dimension) := by
    unfold tameScalarOperator coefficientValue axialValue
    simp_rw [smul_smul, mul_comm (axialPhase _ angle)]
    exact (axialTerm_summable family.property.norm_summable angle).tsum_smul_const _
  rw [operators]
  rfl

theorem coreValue_seedMatrix (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (field : ACore parameters 2) (point : ClosedDisk) (angle : ℝ) :
    coreValue (Gauges.seedMatrixCore parameters seed inside field) point angle =
      harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3) angle (coreValue field point angle) := by
  rw [Gauges.seedMatrixCore_eq_full, coreValue_smoothMultiplier]
  have phase : Grad.GaugeCoefficients.Algebra.fourierPhase = axialPhase := by
    funext cell angle
    exact ((axialPhase_eq_character cell angle).trans (cellCharacter_coe cell angle)).symm
  rw [← phase, Gauges.seedMatrixCells_fourier parameters seed inside]

theorem singleton_coordinate {dimension : ℕ} (coordinate : Fin 2) (jet : ClosedJet dimension) :
    singletonCore parameters (coordinateJet coordinate jet) =
      coordinateCore parameters coordinate (singletonCore parameters jet) := by
  apply acore_ext
  intro cell point
  rw [coordinateCore_val, coordinateJet_value, singletonCore_val, singletonCore_val]
  by_cases zeroCell : cell = 0
  · rw [if_pos zeroCell, if_pos zeroCell, coordinateJet_value]
  · rw [if_neg zeroCell, if_neg zeroCell, closedJet_value_zero, ContinuousMap.zero_apply, smul_zero]

theorem axisDerivative_coordinateConstant {dimension : ℕ} (direction coordinate : Fin 2)
    (vector : ComplexEuclidean dimension) (angle : ℝ) :
    coreValue (partialCore parameters direction (coordinateCore parameters coordinate
      (constantCore parameters vector))) originPoint angle = if direction = coordinate then vector else 0 := by
  have coefficient (cell : ℤ) :
      ((partialCore parameters direction (coordinateCore parameters coordinate
        (constantCore parameters vector))).val cell).value originPoint =
      if direction = coordinate then ((constantCore parameters vector).val cell).value originPoint else 0 :=
    coordinateJet_originPartial direction coordinate ((constantCore parameters vector).val cell)
  unfold coreValue
  simp_rw [coefficient]
  by_cases equal : direction = coordinate
  · simp only [if_pos equal]
    exact coreValue_constant vector originPoint angle
  · simp only [if_neg equal, smul_zero, tsum_zero]

theorem axisDerivative_zeroJets {dimension : ℕ} (field : ACore parameters dimension)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.val cell)) (direction : Fin 2) (angle : ℝ) :
    coreValue (partialCore parameters direction field) originPoint angle = 0 := by
  unfold coreValue
  have coefficient (cell : ℤ) : ((partialCore parameters direction field).val cell).value originPoint = 0 :=
    zeroJets cell 1 le_rfl (fun _ => direction)
  simp_rw [coefficient, smul_zero, tsum_zero]

theorem axisDerivative_tameCoordinate (direction coordinate : Fin 2) (angle : ℝ) :
    coreValue (partialCore parameters direction (tameCoordinateScalarField parameters coordinate)) originPoint angle =
      if direction = coordinate then EuclideanSpace.single 0 1 else 0 := by
  rw [tameCoordinateScalarField, singleton_coordinate]
  exact axisDerivative_coordinateConstant direction coordinate _ angle

theorem axisDerivative_tamePlanarCoordinate (direction : Fin 2) (angle : ℝ) :
    coreValue (partialCore parameters direction (tamePlanarCoordinateField parameters)) originPoint angle =
      EuclideanSpace.single direction 1 := by
  rw [tamePlanarCoordinateField, singleton_coordinate, singleton_coordinate, map_add, coreValue_add]
  change coreValue (partialCore parameters direction (coordinateCore parameters 0
      (constantCore parameters (EuclideanSpace.single 0 1)))) originPoint angle +
    coreValue (partialCore parameters direction (coordinateCore parameters 1
      (constantCore parameters (EuclideanSpace.single 1 1)))) originPoint angle = _
  rw [axisDerivative_coordinateConstant, axisDerivative_coordinateConstant]
  fin_cases direction <;> simp

theorem partialCore_seedMatrix (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (direction : Fin 2) (field : ACore parameters 2) :
    partialCore parameters direction (Gauges.seedMatrixCore parameters seed inside field) =
      Gauges.seedMatrixCore parameters seed inside (partialCore parameters direction field) := by
  rw [Gauges.seedMatrixCore_eq_full, partialCore_smoothMultiplier, ← Gauges.seedMatrixCore_eq_full]

theorem axisDerivative_tameSeedField (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (direction : Fin 2) (angle : ℝ) :
    coreValue (partialCore parameters direction (tameSeedField parameters seed inside)) originPoint angle =
      tamePlanarInclusion (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3) angle
        (EuclideanSpace.single direction 1)) := by
  rw [tameSeedField, partialCore_valueMap, coreValue_valueMap,
    tameSeedPlanarField, partialCore_seedMatrix, coreValue_seedMatrix,
    axisDerivative_tamePlanarCoordinate]

end Grad.NonlinearRange
