import QO8DifferentialReality
import RootUnitIdentity

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 800000

open scoped ComplexConjugate BigOperators

namespace Grad.NonlinearRange

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.GaugeCoefficients.Physical.Frame

variable {parameters : PhaseParameters}

theorem axialPhase_eq_character (cell : ℤ) (angle : ℝ) :
    axialPhase cell angle = cellCharacter cell (angle : CellCircle) := by
  rw [cellCharacter_coe]
  unfold axialPhase cellExponential
  congr 1
  push_cast
  ring

/-- Exact Fourier uniqueness for absolutely summable coefficient families,
using the accepted original-period coefficient recovery. -/
theorem axialSeries_ext {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] [CompleteSpace Value] (first second : ℤ → Value)
    (firstNorms : Summable (fun cell => ‖first cell‖))
    (secondNorms : Summable (fun cell => ‖second cell‖))
    (equalValues : ∀ angle : ℝ, (∑' cell, axialPhase cell angle • first cell) =
      ∑' cell, axialPhase cell angle • second cell) : first = second := by
  have circleEquality : (fun circle : CellCircle => ∑' cell, cellCharacter cell circle • first cell) =
      fun circle : CellCircle => ∑' cell, cellCharacter cell circle • second cell := by
    funext circle
    induction circle using QuotientAddGroup.induction_on with
    | H angle => simpa only [← axialPhase_eq_character] using equalValues angle
  funext cell
  have firstRecovered := seedCircleSeries_coefficient first firstNorms cell
  have secondRecovered := seedCircleSeries_coefficient second secondNorms cell
  rw [circleEquality] at firstRecovered
  exact firstRecovered.symm.trans secondRecovered

theorem coefficientValue_ext {first second : TameCoefficient parameters}
    (equalValues : ∀ angle, coefficientValue first angle = coefficientValue second angle) :
    first = second := by
  apply Subtype.ext
  apply axialSeries_ext first.val second.val first.property.norm_summable second.property.norm_summable
  intro angle
  simpa only [coefficientValue, axialValue, smul_eq_mul, mul_comm] using equalValues angle

/-- The literal chart root satisfies the exact quadratic normalization in
the original coefficient algebra, derived from its proved positive-root law. -/
theorem rootChart_square (family : TangentCoefficient parameters)
    (real : RealTangent family) (axis : RootAxisCondition family) :
    rootChart family ^ 2 + tangentQuadratic family = 1 := by
  apply coefficientValue_ext
  intro angle
  rw [coefficientValue_add, coefficientValue_pow, coefficientValue_one,
    rootChart_value_eq_sqrt real axis, coefficientValue_tangentQuadratic_real real]
  have small := rootAxis_planarValue_lt axis angle
  have nonnegative : 0 ≤ 1 - ‖planarValue family angle‖ ^ 2 / 2 := by linarith
  have identity := Real.sq_sqrt nonnegative
  norm_cast
  linarith

theorem coefficient_reality_of_real_value (family : TameCoefficient parameters)
    (real : ∀ angle, conj (coefficientValue family angle) = coefficientValue family angle) :
    ∀ cell, family.val (-cell) = conj (family.val cell) := by
  have reversedNorms : Summable (fun cell => ‖conj (family.val (-cell))‖) := by
    have summable := (Equiv.neg ℤ).summable_iff.mpr family.property.norm_summable
    change Summable (fun cell => ‖family.val (-cell)‖) at summable
    simpa only [Complex.norm_conj] using summable
  have equality : (fun cell => conj (family.val (-cell))) = family.val := by
    apply axialSeries_ext _ _ reversedNorms family.property.norm_summable
    intro angle
    have original := coefficientValue_hasSum family angle
    have mapped := original.map (starRingEnd ℂ) Complex.continuous_conj
    have reindexed := (Equiv.neg ℤ).hasSum_iff.mpr mapped
    have same : HasSum (fun cell => axialPhase cell angle • conj (family.val (-cell)))
        (coefficientValue family angle) := by
      rw [← real angle]
      apply reindexed.congr_fun
      intro cell
      change axialPhase cell angle • conj (family.val (-cell)) =
        conj (family.val (-cell) * axialPhase (-cell) angle)
      simp only [map_mul, axialPhase_conj, neg_neg, smul_eq_mul, mul_comm]
    have originalSame : HasSum (fun cell => axialPhase cell angle • family.val cell)
        (coefficientValue family angle) := by
      simpa only [smul_eq_mul, mul_comm] using original
    exact same.tsum_eq.trans originalSame.tsum_eq.symm
  intro cell
  have value := congrFun equality (-cell)
  simpa only [neg_neg] using value.symm

theorem rootChart_real (family : TangentCoefficient parameters)
    (real : RealTangent family) (axis : RootAxisCondition family) :
    ∀ cell, (rootChart family).val (-cell) = conj ((rootChart family).val cell) := by
  apply coefficient_reality_of_real_value
  intro angle
  rw [rootChart_value_eq_sqrt real axis, Complex.conj_ofReal]

end Grad.NonlinearRange
