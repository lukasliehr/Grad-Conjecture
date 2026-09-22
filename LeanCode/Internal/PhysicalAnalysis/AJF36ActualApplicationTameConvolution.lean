import AJF12RealSourceApplicationDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped ContDiff BigOperators
namespace Grad.AnnularHighGenerators
open Grad.AnnularOrbitGenerators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A norm estimate for the genuine Leibniz derivatives, retaining the
coefficient/data derivative allocation until the one-high interpolation step. -/
theorem realApplication_tameConvolution
    (operator : ℝ → E →L[ℝ] F) (data : ℝ → E)
    (operatorSmooth : ContDiff ℝ ∞ operator) (dataSmooth : ContDiff ℝ ∞ data)
    (order : ℕ) (time : ℝ) (weight operatorConstant sourceConstant : ℕ → ℝ)
    (operatorNonnegative : ∀ index, 0 ≤ operatorConstant index)
    (target : ℝ)
    (operatorBound : ∀ index ≤ order,
      ‖iteratedDeriv index operator time‖ ≤ operatorConstant index * weight index)
    (mixedSourceBound : ∀ index ≤ order,
      weight index * ‖iteratedDeriv (order - index) data time‖ ≤ sourceConstant index * target) :
    ‖iteratedDeriv order (fun point => operator point (data point)) time‖ ≤
      (∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
        operatorConstant index * sourceConstant index) * target := by
  apply (iteratedDeriv_realOperatorApplication_bound operator data operatorSmooth dataSmooth order time).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index member
  have below : index ≤ order := by have := Finset.mem_range.mp member; omega
  have bound : ‖iteratedDeriv index operator time‖ * ‖iteratedDeriv (order - index) data time‖ ≤
      operatorConstant index * sourceConstant index * target := by
    calc
      _ ≤ (operatorConstant index * weight index) * ‖iteratedDeriv (order - index) data time‖ :=
        mul_le_mul_of_nonneg_right (operatorBound index below) (norm_nonneg _)
      _ = operatorConstant index * (weight index * ‖iteratedDeriv (order - index) data time‖) := by ring
      _ ≤ operatorConstant index * (sourceConstant index * target) :=
        mul_le_mul_of_nonneg_left (mixedSourceBound index below) (operatorNonnegative index)
      _ = operatorConstant index * sourceConstant index * target := by ring
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left bound (by positivity : 0 ≤ (order.choose index : ℝ))

/-- The convolution constant is fixed before any source or retained state. -/
theorem tameConvolutionConstant_nonnegative (order : ℕ) (operatorConstant sourceConstant : ℕ → ℝ)
    (operatorNonnegative : ∀ index, 0 ≤ operatorConstant index)
    (sourceNonnegative : ∀ index, 0 ≤ sourceConstant index) :
    0 ≤ ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) * operatorConstant index * sourceConstant index := by
  apply Finset.sum_nonneg
  intro index _
  exact mul_nonneg (mul_nonneg (by positivity) (operatorNonnegative index)) (sourceNonnegative index)

end Grad.AnnularHighGenerators
