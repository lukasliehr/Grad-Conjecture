import QO6RadialMean
import QO2AffineTrace
import QuotientPolynomialFinal

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

namespace Grad.NonlinearRange

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.AxisSplit Grad.AxisJet Grad.QuotientProjection

variable {parameters : PhaseParameters}

theorem zMulCore_starZMulCore {dimension : ℕ} (field : ACore parameters dimension) :
    zMulCore parameters (starZMulCore parameters field) =
      starZMulCore parameters (zMulCore parameters field) := by
  apply acore_ext
  intro cell point
  rw [zMulCore_jet, coordinateMultiplyJet_value, starZMulCore_jet, coordinateMultiplyJet_value,
    starZMulCore_jet, coordinateMultiplyJet_value, zMulCore_jet, coordinateMultiplyJet_value]
  exact smul_comm _ _ _

theorem spinDerivatives_euler {dimension : ℕ} (field : ACore parameters dimension) :
    starZMulCore parameters (partialPlusCore parameters field) +
      zMulCore parameters (partialMinusCore parameters field) = (2 : ℂ) • eulerCore parameters field := by
  simp only [starZMulCore, zMulCore, partialPlusCore, partialMinusCore, eulerCore,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    map_add, map_sub, map_smul]
  match_scalars <;> ring_nf; norm_num [Complex.I_sq, pow_succ]

theorem dot_zMulCore_left (first second : ACore parameters 3) :
    dotOperation parameters (zMulCore parameters first) second =
      zMulCore parameters (dotOperation parameters first second) := by
  change pairProductLinear parameters physicalDotProduct
    (coordinateCore parameters 0 first + Complex.I • coordinateCore parameters 1 first) second = _
  rw [map_add, map_smul]
  change pairProductLinear parameters physicalDotProduct (coordinateCore parameters 0 first) second +
    Complex.I • pairProductLinear parameters physicalDotProduct (coordinateCore parameters 1 first) second = _
  rw [pairProduct_coordinate_left, pairProduct_coordinate_left]
  rfl

theorem dot_starZMulCore_left (first second : ACore parameters 3) :
    dotOperation parameters (starZMulCore parameters first) second =
      starZMulCore parameters (dotOperation parameters first second) := by
  change pairProductLinear parameters physicalDotProduct
    (coordinateCore parameters 0 first - Complex.I • coordinateCore parameters 1 first) second = _
  rw [map_sub, map_smul]
  change pairProductLinear parameters physicalDotProduct (coordinateCore parameters 0 first) second -
    Complex.I • pairProductLinear parameters physicalDotProduct (coordinateCore parameters 1 first) second = _
  rw [pairProduct_coordinate_left, pairProduct_coordinate_left]
  rfl

theorem spinDot_euler (field : ACore parameters 3) :
    starZMulCore parameters (dotOperation parameters (partialPlusCore parameters field) (rotationCore parameters field)) +
      zMulCore parameters (dotOperation parameters (partialMinusCore parameters field) (rotationCore parameters field)) =
      (2 : ℂ) • dotOperation parameters (eulerCore parameters field) (rotationCore parameters field) := by
  rw [← dot_starZMulCore_left, ← dot_zMulCore_left]
  rw [← LinearMap.add_apply, ← map_add, spinDerivatives_euler, map_smul]
  rfl

theorem quotientPolynomialRows_rawFirstPair (cellLength : ℝ) (state : QuotientState parameters) :
    starZMulCore parameters (quotientPolynomialRows parameters cellLength state 0) +
      zMulCore parameters (quotientPolynomialRows parameters cellLength state 1) =
    (2 : ℂ) • (eulerCore parameters (statePotential state) -
      dotOperation parameters (eulerCore parameters (stateField state)) (rotationCore parameters (stateField state)) +
      radiusSquaredCore parameters (quotientDotCurried parameters (stateField state) (stateField state))) := by
  simp only [quotientPolynomialRows, Matrix.cons_val_zero, Matrix.cons_val_one,
    izConstantCore, negIStarZConstantCore, map_add, map_sub]
  rw [scalarConstantCore_as_smul Complex.I, scalarConstantCore_as_smul (-Complex.I)]
  simp only [map_smul, zMulCore_starZMulCore]
  have derivatives := spinDerivatives_euler (statePotential state)
  have products := spinDot_euler (stateField state)
  change _ = (2 : ℂ) • (eulerCore parameters (statePotential state) -
    dotOperation parameters (eulerCore parameters (stateField state)) (rotationCore parameters (stateField state)) +
    starZMulCore parameters (zMulCore parameters
      (quotientDotCurried parameters (stateField state) (stateField state))))
  calc
    _ = (starZMulCore parameters (partialPlusCore parameters (statePotential state)) +
          zMulCore parameters (partialMinusCore parameters (statePotential state))) -
        (starZMulCore parameters (dotOperation parameters (partialPlusCore parameters (stateField state))
          (rotationCore parameters (stateField state))) +
          zMulCore parameters (dotOperation parameters (partialMinusCore parameters (stateField state))
            (rotationCore parameters (stateField state)))) +
        (2 : ℂ) • starZMulCore parameters (zMulCore parameters
          (quotientDotCurried parameters (stateField state) (stateField state))) := by module
    _ = _ := by rw [derivatives, products]; module

theorem quotientPolynomialRows_rawFirstPair_mean_zero (cellLength : ℝ) (state : QuotientState parameters)
    (gauge : GaugeState parameters state) :
    angularCore parameters 0
      (starZMulCore parameters (quotientPolynomialRows parameters cellLength state 0) +
        zMulCore parameters (quotientPolynomialRows parameters cellLength state 1)) = 0 := by
  rw [quotientPolynomialRows_rawFirstPair, map_smul, map_add, map_sub,
    angularCore_eulerCore_zero (statePotential state) gauge, quotientDot_radial_identity,
    angularCore_projection, if_pos rfl, zero_sub, neg_add_cancel, smul_zero]

theorem quotientPolynomialRows_mode_zero (cellLength : ℝ) (state : QuotientState parameters)
    (gauge : GaugeState parameters state) :
    modeProjection parameters (quotientPolynomialRows parameters cellLength state) = 0 :=
  modeProjection_eq_zero_of_raw_mean _ (quotientPolynomialRows_rawFirstPair_mean_zero cellLength state gauge)

end Grad.NonlinearRange
