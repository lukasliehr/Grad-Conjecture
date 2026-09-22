import AKCV1ExactZeroInverseRemainder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace Grad.NashMoser.BranchDerivative

private theorem quadratic_low_to_two_scale
    (constant coefficient high low : ℝ) (constantNonnegative : 0 ≤ constant)
    (coefficientNonnegative : 0 ≤ coefficient) (lowNonnegative : 0 ≤ low) (lowLeHigh : low ≤ high) :
    constant * (high*low+coefficient*low^2) ≤ (constant*(1+coefficient))*high*low := by
  have square : low^2 ≤ high*low := by
    nlinarith [mul_le_mul_of_nonneg_right lowLeHigh lowNonnegative]
  calc
    _ ≤ constant * (high*low+coefficient*(high*low)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left square coefficientNonnegative)) constantNonnegative
    _ = _ := by ring

/-- Compose the displayed one-high inverse estimate with the two nonlinear
Taylor estimates. All state coefficients are fixed at the base point (or
bounded on its local segment). Only one high difference factor remains;
there is no high-times-high remainder loss. -/
theorem inverse_taylor_two_scale_bound
    {State Source Output HighSource LowSource : Type*}
    [AddCommGroup State] [Module ℝ State] [AddCommGroup Source] [Module ℝ Source]
    [NormedAddCommGroup Output] [NormedSpace ℝ Output]
    [NormedAddCommGroup HighSource] [NormedSpace ℝ HighSource]
    [NormedAddCommGroup LowSource] [NormedSpace ℝ LowSource]
    (inverse : Source →ₗ[ℝ] State) (embedding : State →ₗ[ℝ] Output)
    (highEmbedding : Source →ₗ[ℝ] HighSource) (lowEmbedding : Source →ₗ[ℝ] LowSource)
    (remainder : Source)
    (inverseConstant highConstant lowConstant stateWeight highStateWeight lowStateWeight high low : ℝ)
    (inverseNonnegative : 0 ≤ inverseConstant) (highNonnegative : 0 ≤ highConstant)
    (lowNonnegative : 0 ≤ lowConstant) (stateNonnegative : 0 ≤ stateWeight)
    (highStateNonnegative : 0 ≤ highStateWeight) (lowStateNonnegative : 0 ≤ lowStateWeight)
    (differenceNonnegative : 0 ≤ low) (lowLeHigh : low ≤ high)
    (inverseBound : ‖embedding (inverse remainder)‖ ≤
      inverseConstant * (‖highEmbedding remainder‖+stateWeight*‖lowEmbedding remainder‖))
    (highTaylor : ‖highEmbedding remainder‖ ≤
      highConstant * (high*low+highStateWeight*low^2))
    (lowTaylor : ‖lowEmbedding remainder‖ ≤
      lowConstant * (high*low+lowStateWeight*low^2)) :
    ‖embedding (inverse remainder)‖ ≤
      (inverseConstant * (highConstant*(1+highStateWeight) +
        stateWeight*(lowConstant*(1+lowStateWeight)))) * high * low := by
  have highPaid := highTaylor.trans (quadratic_low_to_two_scale highConstant highStateWeight
    high low highNonnegative highStateNonnegative differenceNonnegative lowLeHigh)
  have lowPaid := lowTaylor.trans (quadratic_low_to_two_scale lowConstant lowStateWeight
    high low lowNonnegative lowStateNonnegative differenceNonnegative lowLeHigh)
  calc
    _ ≤ inverseConstant * (‖highEmbedding remainder‖+stateWeight*‖lowEmbedding remainder‖) := inverseBound
    _ ≤ inverseConstant * ((highConstant*(1+highStateWeight))*high*low+
        stateWeight*((lowConstant*(1+lowStateWeight))*high*low)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add highPaid (mul_le_mul_of_nonneg_left lowPaid stateNonnegative)) inverseNonnegative
    _ = _ := by ring

end Grad.NashMoser.BranchDerivative
