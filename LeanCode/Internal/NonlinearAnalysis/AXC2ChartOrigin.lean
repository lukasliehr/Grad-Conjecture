import AXC1ChartChain

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.ChartAxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.AxisSplit Grad.Q24Realization Grad.SmoothForward
open Grad.NonlinearRange

variable {parameters : PhaseParameters}

theorem smoothMultiplier_origin_zero {inputDimension outputDimension : ℕ}
    (coefficients : ℤ → ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension)
    (summable : ∀ grade, Summable (Multipliers.envelopeTerm parameters grade coefficients))
    (field : ACore parameters inputDimension)
    (vanishes : ∀ cell, originValue (field.val cell) = 0) (cell : ℤ) :
    originValue ((Gauges.smoothMultiplier parameters coefficients summable field).val cell) = 0 := by
  change ((Gauges.smoothMultiplier parameters coefficients summable field).val cell).value originPoint = 0
  rw [← (Gauges.smoothMultiplier_value_hasSum parameters coefficients summable field cell originPoint).tsum_eq]
  have term (shift : ℤ) : coefficients shift ((field.val (cell - shift)).value originPoint) = 0 := by
    change coefficients shift (originValue (field.val (cell - shift))) = 0
    rw [vanishes, map_zero]
  simp only [term, tsum_zero]

theorem tameScalarMultiplier_origin_zero {dimension : ℕ} [Nontrivial (ComplexEuclidean dimension)]
    (coefficient : TameCoefficient parameters) (field : ACore parameters dimension)
    (vanishes : ∀ cell, originValue (field.val cell) = 0) (cell : ℤ) :
    originValue ((tameScalarMultiplier dimension coefficient field).val cell) = 0 :=
  smoothMultiplier_origin_zero _ _ field vanishes cell

theorem tameCoordinate_origin_zero (coordinate : Fin 2) (cell : ℤ) :
    originValue ((tameCoordinateScalarField parameters coordinate).val cell) = 0 := by
  rw [tameCoordinateScalarField, singleton_coordinate, coordinateCore_val, coordinateJet_originValue]

theorem tamePlanarCoordinate_origin_zero (cell : ℤ) :
    originValue ((tamePlanarCoordinateField parameters).val cell) = 0 := by
  rw [tamePlanarCoordinateField, acore_val_add, originValue_add,
    singleton_coordinate, singleton_coordinate, coordinateCore_val, coordinateCore_val,
    coordinateJet_originValue, coordinateJet_originValue, add_zero]

theorem tameSeedField_origin_zero (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (cell : ℤ) : originValue ((tameSeedField parameters seed inside).val cell) = 0 := by
  rw [tameSeedField, valueMapCore_originValue, tameSeedPlanarField, Gauges.seedMatrixCore_eq_full,
    smoothMultiplier_origin_zero _ _ _ tamePlanarCoordinate_origin_zero, map_zero]

theorem tameScalarMultiplier_valueMap {inputDimension outputDimension : ℕ}
    [Nontrivial (ComplexEuclidean inputDimension)] [Nontrivial (ComplexEuclidean outputDimension)]
    (coefficient : TameCoefficient parameters)
    (mapping : ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension)
    (field : ACore parameters inputDimension) :
    tameScalarMultiplier outputDimension coefficient (valueMapCore parameters mapping field) =
      valueMapCore parameters mapping (tameScalarMultiplier inputDimension coefficient field) := by
  apply coreValue_ext
  intro point angle
  rw [coreValue_tameScalarMultiplier, coreValue_valueMap, coreValue_valueMap,
    coreValue_tameScalarMultiplier, map_smul]

/-- The shared literal affine field formula for the normalized chart and
its first derivative. The coefficient is actual root or root derivative. -/
def chartAffineField (parameters : PhaseParameters) (seed : Seed.Parameters)
    (inside : seed ∈ Seed.parameterDomain) (coefficient : TameCoefficient parameters)
    (tangent : TangentCoefficient parameters) (remainder : ACore parameters 3) : ACore parameters 3 :=
  tameScalarMultiplier 3 coefficient (tameSeedField parameters seed inside) +
    valueMapCore parameters tameTangentInclusion
      (tameScalarMultiplier 1 (tangentComponent tangent 0) (tameCoordinateScalarField parameters 0) +
        tameScalarMultiplier 1 (tangentComponent tangent 1) (tameCoordinateScalarField parameters 1)) + remainder

theorem chartAffineField_origin_zero (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters)
    (remainder : ACore parameters 3) (vanishes : ∀ cell, originValue (remainder.val cell) = 0)
    (cell : ℤ) :
    originValue ((chartAffineField parameters seed inside coefficient tangent remainder).val cell) = 0 := by
  rw [chartAffineField, acore_val_add, originValue_add, acore_val_add, originValue_add,
    tameScalarMultiplier_origin_zero _ _ (tameSeedField_origin_zero seed inside),
    valueMapCore_originValue, acore_val_add, originValue_add,
    tameScalarMultiplier_origin_zero _ _ (tameCoordinate_origin_zero 0),
    tameScalarMultiplier_origin_zero _ _ (tameCoordinate_origin_zero 1),
    add_zero, map_zero, zero_add, vanishes, add_zero]

end Grad.ChartAxisSplit
