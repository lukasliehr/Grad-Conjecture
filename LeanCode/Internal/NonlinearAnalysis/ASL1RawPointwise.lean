import AXP4PhysicalConsumers

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

namespace Grad.AxisSourceLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.QuotientProjection Grad.RawForward Grad.AxisJet

variable {parameters : PhaseParameters}

def coefficientValue {dimension : ℕ} (cell : ℤ) (point : ClosedDisk) :
    ACore parameters dimension →ₗ[ℂ] ComplexEuclidean dimension where
  toFun field := (field.val cell).value point
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coordinate_ne_zero {point : SpatialPlane} (offAxis : point ≠ 0) :
    signedComplexCoordinate 1 point ≠ 0 := by
  intro vanishes
  have first : point 0 = 0 := by
    simpa [signedComplexCoordinate] using congrArg Complex.re vanishes
  have second : point 1 = 0 := by
    simpa [signedComplexCoordinate] using congrArg Complex.im vanishes
  apply offAxis
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> assumption

/-- Literal J_Y is pointwise injective off the axis, in its original row order. -/
theorem rawReconstruction_pointwise_injective (rows : QuotientRows parameters)
    (cell : ℤ) (point : ClosedDisk) (offAxis : point.val ≠ 0)
    (rawZero : ∀ row, ((rawReconstructionCore parameters rows row).val cell).value point = 0) :
    ∀ row, ((rows row).val cell).value point = 0 := by
  let ev := coefficientValue (parameters := parameters) (dimension := 1) cell point
  have first := rawZero 0
  have second := rawZero 1
  rw [rawReconstructionCore_apply] at first second
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one] at first second
  change ev ((2 * Complex.I)⁻¹ • (starZMulCore parameters (rows 0) -
    zMulCore parameters (rows 1))) = 0 at first
  change ev ((1 / 2 : ℂ) • (starZMulCore parameters (rows 0) +
    zMulCore parameters (rows 1))) = 0 at second
  rw [map_smul, map_sub] at first
  rw [map_smul, map_add] at second
  have difference := (smul_eq_zero.mp first).resolve_left (by simp)
  have sumZero := (smul_eq_zero.mp second).resolve_left (by norm_num)
  have equal := sub_eq_zero.mp difference
  have leftZero : ev (starZMulCore parameters (rows 0)) = 0 := by
    have twice : (2 : ℂ) • ev (starZMulCore parameters (rows 0)) = 0 := by
      simpa only [two_smul, ← equal] using sumZero
    exact (smul_eq_zero.mp twice).resolve_left (by norm_num)
  have rightZero : ev (zMulCore parameters (rows 1)) = 0 := equal.symm.trans leftZero
  have firstZero : ev (rows 0) = 0 := by
    change ((starZMulCore parameters (rows 0)).val cell).value point = 0 at leftZero
    rw [starZMulCore_jet, coordinateMultiplyJet_value] at leftZero
    exact (smul_eq_zero.mp leftZero).resolve_left (starCoordinate_ne_zero offAxis)
  have secondZero : ev (rows 1) = 0 := by
    change ((zMulCore parameters (rows 1)).val cell).value point = 0 at rightZero
    rw [zMulCore_jet, coordinateMultiplyJet_value] at rightZero
    exact (smul_eq_zero.mp rightZero).resolve_left (coordinate_ne_zero offAxis)
  have thirdZero := rawZero 3
  rw [rawReconstructionCore_apply] at thirdZero
  change ((radiusSquaredCore parameters (rows 2)).val cell).value point = 0 at thirdZero
  rw [radiusSquaredCore_value] at thirdZero
  have determinantZero : ev (rows 2) = 0 :=
    (smul_eq_zero.mp thirdZero).resolve_left (pow_ne_zero 2 (norm_ne_zero_iff.mpr offAxis))
  intro row
  fin_cases row
  · exact firstZero
  · exact secondZero
  · exact determinantZero
  · exact rawZero 2

end Grad.AxisSourceLift
