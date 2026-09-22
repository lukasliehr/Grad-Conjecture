import RootUnitInterface
import RootUnitScalar

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! Q14: the literal series realization of the chart root and its pointwise
identification with the positive square root on the literal Q13 ball. -/

variable {parameters : PhaseParameters}

/-- The order-zero shifted coefficients are the literal Q7 coefficients. -/
theorem rootDerivativeCoefficient_zero_order (p : ℕ) :
    rootDerivativeCoefficient 0 p = rootCoefficient p := by
  rw [rootDerivativeCoefficient, Nat.add_zero, Nat.descFactorial_zero, Nat.cast_one, mul_one]

/-- The literal Q7/Q8 series realization of the chart root, cell by cell. -/
theorem rootChart_hasSum {family : TangentCoefficient parameters}
    (small : coefficientEnvelope 0 (tangentQuadratic family) < 1) (cell : ℤ) :
    HasSum (fun p => ((rootCoefficient p : ℝ) : ℂ) * ((tangentQuadratic family) ^ p).val cell)
      ((rootChart family).val cell) := by
  have series := rootShiftedSeries_hasSum 0 (tangentQuadratic family) small cell
  rw [rootChart, tameRootShifted_of_small 0 small]
  have fun_eq : (fun p => ((((rootDerivativeCoefficient 0 p : ℝ) : ℂ) •
      (tangentQuadratic family) ^ p).val cell)) =
      fun p => ((rootCoefficient p : ℝ) : ℂ) * ((tangentQuadratic family) ^ p).val cell := by
    funext p
    rw [tameSmul_val, Pi.smul_apply, smul_eq_mul, rootDerivativeCoefficient_zero_order]
  rw [fun_eq] at series
  exact series

/-- The value of the chart root is the scalar series at the value of the
quadratic: evaluation commutes with the majorized series and is a ring
homomorphism. -/
theorem rootChart_value_hasSum {family : TangentCoefficient parameters}
    (small : coefficientEnvelope 0 (tangentQuadratic family) < 1) (zeta : ℝ) :
    HasSum (fun p => ((rootCoefficient p : ℝ) : ℂ) *
        coefficientValue (tangentQuadratic family) zeta ^ p)
      (coefficientValue (rootChart family) zeta) := by
  have series := coefficientValue_tameSeries _ (rootSeriesMajorant_is_majorant 0 small) zeta
  rw [rootChart, tameRootShifted_of_small 0 small, rootShiftedSeries]
  have fun_eq : (fun p => coefficientValue (((rootDerivativeCoefficient 0 p : ℝ) : ℂ) •
      (tangentQuadratic family) ^ p) zeta) =
      fun p => ((rootCoefficient p : ℝ) : ℂ) *
        coefficientValue (tangentQuadratic family) zeta ^ p := by
    funext p
    rw [coefficientValue_smul, coefficientValue_pow, rootDerivativeCoefficient_zero_order]
  rw [fun_eq] at series
  exact series

/-- Q14: on the literal Q13 ball, the chart root of a real planar family
evaluates pointwise to the positive square root `√(1 - |τ(ζ)|²/2)`. -/
theorem rootChart_value_eq_sqrt {family : TangentCoefficient parameters}
    (real : RealTangent family) (axis : RootAxisCondition family) (zeta : ℝ) :
    coefficientValue (rootChart family) zeta =
      ((Real.sqrt (1 - ‖planarValue family zeta‖ ^ 2 / 2) : ℝ) : ℂ) := by
  have small := rootAxis_quadratic_small axis
  have r_lt := rootAxis_planarValue_lt axis zeta
  have r_nonneg : (0 : ℝ) ≤ ‖planarValue family zeta‖ ^ 2 / 2 := by positivity
  have r_abs : |‖planarValue family zeta‖ ^ 2 / 2| ≤ 1 / 8 := by
    rw [abs_of_nonneg r_nonneg]
    exact r_lt.le
  have series := rootChart_value_hasSum small zeta
  rw [coefficientValue_tangentQuadratic_real real zeta] at series
  have scalar := rootScalar_hasSum_complex (lt_of_le_of_lt r_abs (by norm_num))
  rw [series.unique scalar, rootScalar_eq_sqrt r_abs]

end Grad.NonlinearQuotientBounds
