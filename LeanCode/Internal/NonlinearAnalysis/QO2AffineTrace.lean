import QO1AxisAlgebra

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

namespace Grad.NonlinearRange

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.AxisSplit Grad.AxisJet Grad.QuotientProjection

variable {parameters : PhaseParameters}

theorem traceFirst_zMulCore_zero {dimension : ℕ} (field : ACore parameters dimension) :
    traceFirst 0 (zMulCore parameters field) = traceZero field := by
  change traceFirst 0 (coordinateCore parameters 0 field + Complex.I • coordinateCore parameters 1 field) = _
  rw [map_add, map_smul, traceFirst_coordinateCore, traceFirst_coordinateCore,
    if_pos rfl, if_neg (by decide : ¬(0 : Fin 2) = 1), smul_zero, add_zero]

theorem traceFirst_zMulCore_one {dimension : ℕ} (field : ACore parameters dimension) :
    traceFirst 1 (zMulCore parameters field) = Complex.I • traceZero field := by
  change traceFirst 1 (coordinateCore parameters 0 field + Complex.I • coordinateCore parameters 1 field) = _
  rw [map_add, map_smul, traceFirst_coordinateCore, traceFirst_coordinateCore,
    if_neg (by decide : ¬(1 : Fin 2) = 0), if_pos rfl, zero_add]

theorem traceFirst_starZMulCore_zero {dimension : ℕ} (field : ACore parameters dimension) :
    traceFirst 0 (starZMulCore parameters field) = traceZero field := by
  change traceFirst 0 (coordinateCore parameters 0 field - Complex.I • coordinateCore parameters 1 field) = _
  rw [map_sub, map_smul, traceFirst_coordinateCore, traceFirst_coordinateCore,
    if_pos rfl, if_neg (by decide : ¬(0 : Fin 2) = 1), smul_zero, sub_zero]

theorem traceFirst_starZMulCore_one {dimension : ℕ} (field : ACore parameters dimension) :
    traceFirst 1 (starZMulCore parameters field) = -Complex.I • traceZero field := by
  change traceFirst 1 (coordinateCore parameters 0 field - Complex.I • coordinateCore parameters 1 field) = _
  rw [map_sub, map_smul, traceFirst_coordinateCore, traceFirst_coordinateCore,
    if_neg (by decide : ¬(1 : Fin 2) = 0), if_pos rfl, zero_sub]
  module

theorem scalarConstantCore_as_smul (scalar : ℂ) :
    scalarConstantCore parameters scalar = scalar • scalarConstantCore parameters 1 := by
  apply acore_ext
  intro cell point
  rw [acore_smul_value]
  by_cases zero : cell = 0
  · subst cell
    change ((constantCore parameters (EuclideanSpace.single 0 scalar)).val 0).value point =
      scalar • ((constantCore parameters (EuclideanSpace.single 0 1)).val 0).value point
    rw [constantCore_value_zero, constantCore_value_zero]
    ext coordinate
    fin_cases coordinate
    simp
  · rw [show scalarConstantCore parameters scalar = constantCore parameters (EuclideanSpace.single 0 scalar) from rfl,
      show scalarConstantCore parameters 1 = constantCore parameters (EuclideanSpace.single 0 1) from rfl,
      constantCore_value_ne _ zero, constantCore_value_ne _ zero, smul_zero]

/-- O20 expressed in the exact coefficient-space affine trace. It is an
identity for arbitrary smooth fields, before imposing normalization. -/
theorem quotientPolynomialRows_affineTrace (cellLength : ℝ) (state : QuotientState parameters) :
    affineTrace parameters (quotientPolynomialRows parameters cellLength state) =
      traceZero (scalarConstantCore parameters 1) - (1 / 2 : ℂ) •
        traceZero (dotOperation parameters (partialCore parameters 0 (stateField state))
          (partialCore parameters 0 (stateField state)) +
          dotOperation parameters (partialCore parameters 1 (stateField state))
            (partialCore parameters 1 (stateField state))) := by
  change (4 * Complex.I)⁻¹ •
    ((traceFirst 0 (quotientPolynomialRows parameters cellLength state 0) -
      Complex.I • traceFirst 1 (quotientPolynomialRows parameters cellLength state 0)) -
    (traceFirst 0 (quotientPolynomialRows parameters cellLength state 1) +
      Complex.I • traceFirst 1 (quotientPolynomialRows parameters cellLength state 1))) = _
  simp only [quotientPolynomialRows, Matrix.cons_val_zero, Matrix.cons_val_one,
    izConstantCore, negIStarZConstantCore, map_add, map_sub,
    traceFirst_dot_rotation_zero, traceFirst_dot_rotation_one,
    traceFirst_zMulCore_zero, traceFirst_zMulCore_one,
    traceFirst_starZMulCore_zero, traceFirst_starZMulCore_one]
  simp only [partialPlusCore, partialMinusCore, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply]
  rw [traceFirst_partialCore_commute (parameters := parameters) 1 0]
  rw [scalarConstantCore_as_smul Complex.I, scalarConstantCore_as_smul (-Complex.I)]
  simp only [map_smul, smul_smul, smul_add, smul_sub]
  norm_num
  match_scalars <;> ring_nf <;> norm_num [Complex.I_sq, pow_succ]

end Grad.NonlinearRange
