import QX1RawReconstruction

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

namespace Grad.RawForward

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.QuotientProjection

variable {parameters : PhaseParameters}

theorem spinDerivatives_rotation {dimension : ℕ} (field : ACore parameters dimension) :
    starZMulCore parameters (partialPlusCore parameters field) -
      zMulCore parameters (partialMinusCore parameters field) =
    (2 * Complex.I) • rotationCore parameters field := by
  simp only [starZMulCore, zMulCore, partialPlusCore, partialMinusCore, rotationCore,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    map_add, map_sub, map_smul]
  match_scalars <;> ring

theorem spinDot_rotation (field : ACore parameters 3) :
    starZMulCore parameters (dotOperation parameters (partialPlusCore parameters field) (rotationCore parameters field)) -
      zMulCore parameters (dotOperation parameters (partialMinusCore parameters field) (rotationCore parameters field)) =
    (2 * Complex.I) • dotOperation parameters (rotationCore parameters field) (rotationCore parameters field) := by
  rw [← dot_starZMulCore_left, ← dot_zMulCore_left]
  calc
    _ = dotOperation parameters
      (starZMulCore parameters (partialPlusCore parameters field) -
        zMulCore parameters (partialMinusCore parameters field)) (rotationCore parameters field) := by
      rw [map_sub]
      rfl
    _ = _ := by rw [spinDerivatives_rotation, map_smul]; rfl

theorem quotientPolynomialRows_rawDifference (cellLength : ℝ) (state : QuotientState parameters) :
    starZMulCore parameters (quotientPolynomialRows parameters cellLength state 0) -
      zMulCore parameters (quotientPolynomialRows parameters cellLength state 1) =
    (2 * Complex.I) • originalRawRowsCore parameters cellLength state 0 := by
  simp only [quotientPolynomialRows, Matrix.cons_val_zero, Matrix.cons_val_one,
    izConstantCore, negIStarZConstantCore, map_add, map_sub]
  rw [scalarConstantCore_as_smul Complex.I, scalarConstantCore_as_smul (-Complex.I)]
  simp only [map_smul, zMulCore_starZMulCore]
  have derivatives := spinDerivatives_rotation (statePotential state)
  have products := spinDot_rotation (stateField state)
  change _ = (2 * Complex.I) • (rotationCore parameters (statePotential state) -
    dotOperation parameters (rotationCore parameters (stateField state)) (rotationCore parameters (stateField state)) +
    starZMulCore parameters (zMulCore parameters (scalarConstantCore parameters 1)))
  calc
    _ = (starZMulCore parameters (partialPlusCore parameters (statePotential state)) -
        zMulCore parameters (partialMinusCore parameters (statePotential state))) -
      (starZMulCore parameters (dotOperation parameters (partialPlusCore parameters (stateField state))
        (rotationCore parameters (stateField state))) -
       zMulCore parameters (dotOperation parameters (partialMinusCore parameters (stateField state))
        (rotationCore parameters (stateField state)))) +
      (2 * Complex.I) • starZMulCore parameters (zMulCore parameters (scalarConstantCore parameters 1)) := by module
    _ = _ := by rw [derivatives, products]; module

theorem quotientPolynomialRows_rawSum (cellLength : ℝ) (state : QuotientState parameters)
    (gauge : GaugeState parameters state) :
    starZMulCore parameters (quotientPolynomialRows parameters cellLength state 0) +
      zMulCore parameters (quotientPolynomialRows parameters cellLength state 1) =
    (2 : ℂ) • originalRawRowsCore parameters cellLength state 1 := by
  rw [quotientPolynomialRows_rawFirstPair, quotientDot_radial_identity]
  change _ = (2 : ℂ) • ((eulerCore parameters (statePotential state) -
    dotOperation parameters (eulerCore parameters (stateField state)) (rotationCore parameters (stateField state))) -
    angularCore parameters 0 (eulerCore parameters (statePotential state) -
      dotOperation parameters (eulerCore parameters (stateField state)) (rotationCore parameters (stateField state))))
  rw [map_sub, angularCore_eulerCore_zero (statePotential state) gauge]
  module

theorem rawReconstruction_first (cellLength : ℝ) (state : QuotientState parameters) :
    rawReconstructionCore parameters (quotientPolynomialRows parameters cellLength state) 0 =
      originalRawRowsCore parameters cellLength state 0 := by
  change (2 * Complex.I)⁻¹ • (starZMulCore parameters (quotientPolynomialRows parameters cellLength state 0) -
    zMulCore parameters (quotientPolynomialRows parameters cellLength state 1)) = _
  rw [quotientPolynomialRows_rawDifference, smul_smul,
    inv_mul_cancel₀ (mul_ne_zero (by norm_num) Complex.I_ne_zero), one_smul]

theorem rawReconstruction_second (cellLength : ℝ) (state : QuotientState parameters)
    (gauge : GaugeState parameters state) :
    rawReconstructionCore parameters (quotientPolynomialRows parameters cellLength state) 1 =
      originalRawRowsCore parameters cellLength state 1 := by
  change (1 / 2 : ℂ) • (starZMulCore parameters (quotientPolynomialRows parameters cellLength state 0) +
    zMulCore parameters (quotientPolynomialRows parameters cellLength state 1)) = _
  rw [quotientPolynomialRows_rawSum cellLength state gauge, smul_smul]
  norm_num

theorem rawReconstruction_third (cellLength : ℝ) (state : QuotientState parameters) :
    rawReconstructionCore parameters (quotientPolynomialRows parameters cellLength state) 2 =
      originalRawRowsCore parameters cellLength state 2 := rfl

end Grad.RawForward
