import QO1AxisAlgebra
import DivisionUniqueness

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

open scoped BigOperators Topology
open Filter

namespace Grad.NonlinearRange

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.AxisSplit Grad.AxisJet Grad.QuotientProjection

variable {parameters : PhaseParameters}

theorem zMulCore_jet {dimension : ℕ} (field : ACore parameters dimension) (cell : ℤ) :
    (zMulCore parameters field).val cell = coordinateMultiplyJet 1 (field.val cell) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change (coordinateJet 0 (field.val cell) + Complex.I • coordinateJet 1 (field.val cell)).value point = _
  rw [closedJet_value_add, closedJet_value_smul, ContinuousMap.add_apply,
    ContinuousMap.smul_apply, coordinateJet_value, coordinateJet_value, coordinateMultiplyJet_value]
  simp only [signedComplexCoordinate, Complex.ofReal_one, mul_one, add_smul, mul_smul,
    Complex.coe_smul]

theorem starZMulCore_jet {dimension : ℕ} (field : ACore parameters dimension) (cell : ℤ) :
    (starZMulCore parameters field).val cell = coordinateMultiplyJet (-1) (field.val cell) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change (coordinateJet 0 (field.val cell) - Complex.I • coordinateJet 1 (field.val cell)).value point = _
  rw [sub_eq_add_neg, closedJet_value_add, closedJet_value_neg, closedJet_value_smul,
    ContinuousMap.add_apply, ContinuousMap.neg_apply, ContinuousMap.smul_apply,
    coordinateJet_value, coordinateJet_value, coordinateMultiplyJet_value]
  simp only [signedComplexCoordinate, Complex.ofReal_neg, Complex.ofReal_one,
    mul_neg_one, neg_mul, add_smul, neg_smul, mul_smul, Complex.coe_smul]

theorem angularCore_zMulCore {dimension : ℕ} (mode : ℤ) (field : ACore parameters dimension) :
    angularCore parameters mode (zMulCore parameters field) =
      zMulCore parameters (angularCore parameters (mode - 1) field) := by
  apply Subtype.ext
  funext cell
  rw [angularCore_apply, zMulCore_jet, angularClosedJet_z, zMulCore_jet, angularCore_apply]

theorem angularCore_starZMulCore {dimension : ℕ} (mode : ℤ) (field : ACore parameters dimension) :
    angularCore parameters mode (starZMulCore parameters field) =
      starZMulCore parameters (angularCore parameters (mode + 1) field) := by
  apply Subtype.ext
  funext cell
  rw [angularCore_apply, starZMulCore_jet, angularClosedJet_zbar, starZMulCore_jet, angularCore_apply]

theorem reflection_mean (field : ACore parameters 1) :
    reflection parameters (angularCore parameters 0 field) = angularCore parameters 0 field := by
  apply Subtype.ext
  funext cell
  exact reflection_mean_jet (field.val cell)

theorem reflection_starZMulCore (field : ACore parameters 1) :
    reflection parameters (starZMulCore parameters field) =
      zMulCore parameters (reflection parameters field) := by
  apply Subtype.ext
  funext cell
  change orthogonalJet cartesianReflectionEquiv ((starZMulCore parameters field).val cell) = _
  rw [starZMulCore_jet, reflection_coordinate_zbar, zMulCore_jet]
  rfl

theorem reflection_zMulCore (field : ACore parameters 1) :
    reflection parameters (zMulCore parameters field) =
      starZMulCore parameters (reflection parameters field) := by
  have equality := congrArg (reflection parameters) (reflection_starZMulCore (reflection parameters field))
  rw [reflection_involutive, reflection_involutive] at equality
  exact equality.symm

theorem zMulCore_negative_mode (field : ACore parameters 1) :
    zMulCore parameters (angularCore parameters (-1) field) =
      starZMulCore parameters (reflection parameters (angularCore parameters (-1) field)) := by
  have mean : angularCore parameters 0 (zMulCore parameters (angularCore parameters (-1) field)) =
      zMulCore parameters (angularCore parameters (-1) field) := by
    rw [angularCore_zMulCore]
    rw [show (0 : ℤ) - 1 = -1 by norm_num, angularCore_projection, if_pos rfl]
  have fixed := reflection_mean (zMulCore parameters (angularCore parameters (-1) field))
  rw [mean, reflection_zMulCore] at fixed
  exact fixed.symm

/-- The mean of the raw first pair is exactly the N34 mode obstruction
multiplied by `2 z-bar`; this is a literal identity, not a projection. -/
theorem rawFirstPair_mean (field : SmoothQuotient parameters) :
    angularCore parameters 0 (starZMulCore parameters (field 0) + zMulCore parameters (field 1)) =
      (2 : ℂ) • starZMulCore parameters (firstMode parameters field) := by
  rw [map_add, angularCore_starZMulCore, angularCore_zMulCore]
  norm_num only [zero_add, zero_sub]
  rw [zMulCore_negative_mode, firstMode_apply, map_smul, map_add]
  module

end Grad.NonlinearRange
