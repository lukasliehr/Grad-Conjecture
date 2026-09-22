import AXC2ChartOrigin

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.ChartAxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.AxisSplit Grad.Q24Realization Grad.SmoothForward
open Grad.NonlinearRange

variable {parameters : PhaseParameters}

theorem tameScalarMultiplier_constant_origin {dimension : ℕ} [Nontrivial (ComplexEuclidean dimension)]
    (coefficient : TameCoefficient parameters) (vector : ComplexEuclidean dimension) (cell : ℤ) :
    originValue ((tameScalarMultiplier dimension coefficient (constantCore parameters vector)).val cell) =
      coefficient.val cell • vector := by
  change ((tameScalarMultiplier dimension coefficient (constantCore parameters vector)).val cell).value originPoint = _
  rw [← (tameScalarMultiplier_value_hasSum dimension coefficient
    (constantCore parameters vector) cell originPoint).tsum_eq, tsum_eq_single cell]
  · rw [sub_self, constantCore_value_zero]
  · intro shift different
    rw [constantCore_value_ne vector (sub_ne_zero.mpr different.symm), smul_zero]

theorem tameScalarMultiplier_coordinate_originPartial
    (coefficient : TameCoefficient parameters) (coordinate direction : Fin 2) (cell : ℤ) :
    originPartial direction ((tameScalarMultiplier 1 coefficient
      (tameCoordinateScalarField parameters coordinate)).val cell) =
      if direction = coordinate then coefficient.val cell • EuclideanSpace.single 0 1 else 0 := by
  have value (index : ℤ) : originPartial direction ((tameCoordinateScalarField parameters coordinate).val index) =
      if direction = coordinate then originValue ((constantCore parameters (EuclideanSpace.single 0 1)).val index) else 0 := by
    rw [tameCoordinateScalarField, singleton_coordinate, coordinateCore_val, coordinateJet_originPartial]
    rfl
  change ((partialCore parameters direction (tameScalarMultiplier 1 coefficient
    (tameCoordinateScalarField parameters coordinate))).val cell).value originPoint = _
  rw [partialCore_tameScalarMultiplier,
    ← (tameScalarMultiplier_value_hasSum 1 coefficient
      (partialCore parameters direction (tameCoordinateScalarField parameters coordinate)) cell originPoint).tsum_eq]
  change (∑' shift, coefficient.val shift •
    originPartial direction ((tameCoordinateScalarField parameters coordinate).val (cell - shift))) = _
  simp_rw [value]
  by_cases hit : direction = coordinate
  · simp only [if_pos hit]
    exact (tameScalarMultiplier_value_hasSum 1 coefficient
      (constantCore parameters (EuclideanSpace.single 0 1)) cell originPoint).tsum_eq.trans
        (tameScalarMultiplier_constant_origin coefficient _ cell)
  · simp only [if_neg hit, smul_zero, tsum_zero]

theorem chartAffineField_tangential_partial (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters)
    (remainder : ACore parameters 3)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (remainder.val cell))
    (direction : Fin 2) (cell : ℤ) :
    originPartial direction ((chartAffineField parameters seed inside coefficient tangent remainder).val cell) 1 =
      tangent.val cell direction := by
  have rest : originPartial direction (remainder.val cell) = 0 :=
    zeroJets cell 1 le_rfl (fun _ => direction)
  rw [chartAffineField, acore_val_add, originPartial_add, acore_val_add, originPartial_add,
    tameSeedField, tameScalarMultiplier_valueMap, valueMapCore_val, valueMapJet_originPartial,
    valueMapCore_val, valueMapJet_originPartial, acore_val_add, originPartial_add,
    tameScalarMultiplier_coordinate_originPartial, tameScalarMultiplier_coordinate_originPartial,
    rest]
  change (0 +
      ((if direction = 0 then (tangentComponent tangent 0).val cell • EuclideanSpace.single (0 : Fin 1) (1 : ℂ) else 0) +
        (if direction = 1 then (tangentComponent tangent 1).val cell • EuclideanSpace.single (0 : Fin 1) (1 : ℂ) else 0)) 0) + 0 = _
  fin_cases direction <;> simp [tangentComponent_val]

theorem chartAffineField_tangential_gradient (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters)
    (remainder : ACore parameters 3)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (remainder.val cell)) (cell : ℤ) :
    tangentialOriginGradient (chartAffineField parameters seed inside coefficient tangent remainder) cell =
      tangent.val cell := by
  unfold tangentialOriginGradient
  rw [chartAffineField_tangential_partial seed inside coefficient tangent remainder zeroJets,
    chartAffineField_tangential_partial seed inside coefficient tangent remainder zeroJets]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> rfl

end Grad.ChartAxisSplit
