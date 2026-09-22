import BKB22NeumannInverse

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace

theorem fullKernelAdd_moment_le {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (moment : ℕ)
    (first second : FullTwoFrequencyKernel parameters sourceDimension targetDimension) :
    fullKernelMoment parameters moment (fullKernelAdd first second) ≤
      fullKernelMoment parameters moment first +
        fullKernelMoment parameters moment second := by
  unfold fullKernelMoment
  have rightSummable := (first.moments moment).add (second.moments moment)
  calc
    (∑' shift : ℤ × ℤ,
      boundaryCoefficientPhaseCost parameters shift *
        annularFrequency shift.1 shift.2 ^ moment *
          (fullKernelAdd first second).entryNorm shift) ≤
        ∑' shift : ℤ × ℤ,
          (boundaryCoefficientPhaseCost parameters shift *
              annularFrequency shift.1 shift.2 ^ moment * first.entryNorm shift +
            boundaryCoefficientPhaseCost parameters shift *
              annularFrequency shift.1 shift.2 ^ moment * second.entryNorm shift) :=
      ((fullKernelAdd first second).moments moment).tsum_le_tsum
        (fun shift => by
          calc
            boundaryCoefficientPhaseCost parameters shift *
                  annularFrequency shift.1 shift.2 ^ moment *
                    (fullKernelAdd first second).entryNorm shift ≤
                boundaryCoefficientPhaseCost parameters shift *
                  annularFrequency shift.1 shift.2 ^ moment *
                    (first.entryNorm shift + second.entryNorm shift) :=
              mul_le_mul_of_nonneg_left (fullKernelAdd_entryNorm_le first second shift)
                (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters shift)
                  (pow_nonneg (annularFrequency_pos shift).le moment))
            _ = _ := by ring)
        rightSummable
    _ = (∑' shift : ℤ × ℤ,
          boundaryCoefficientPhaseCost parameters shift *
            annularFrequency shift.1 shift.2 ^ moment * first.entryNorm shift) +
        ∑' shift : ℤ × ℤ,
          boundaryCoefficientPhaseCost parameters shift *
            annularFrequency shift.1 shift.2 ^ moment * second.entryNorm shift :=
      (first.moments moment).tsum_add (second.moments moment)

theorem fullKernelNeg_moment_le {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (moment : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension) :
    fullKernelMoment parameters moment (fullKernelNeg kernel) ≤
      fullKernelMoment parameters moment kernel := by
  unfold fullKernelMoment
  exact ((fullKernelNeg kernel).moments moment).tsum_le_tsum
    (fun shift => mul_le_mul_of_nonneg_left
      (fullKernelNeg_entryNorm_le kernel shift)
      (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters shift)
        (pow_nonneg (annularFrequency_pos shift).le moment)))
    (kernel.moments moment)

theorem fullKernelNeumannSum_moment_le {dimension : ℕ}
    (parameters : PhaseParameters) (moment : ℕ)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) :
    fullKernelMoment parameters moment
        (fullKernelNeumannSum parameters kernel low lowBound lowSmall) ≤
      fullKernelMoment parameters moment
          (fullIdentityKernel parameters dimension) +
        fullKernelNeumannConstant moment low *
          fullKernelMoment parameters moment kernel := by
  apply (fullKernelAdd_moment_le parameters moment
    (fullIdentityKernel parameters dimension)
    (fullKernelNeumannTail parameters kernel low lowBound lowSmall)).trans
  exact add_le_add le_rfl
    (fullKernelNeumannTail_moment_le parameters moment kernel low lowBound lowSmall)

theorem fullKernelNegativeIdentityInverse_moment_le {dimension : ℕ}
    (parameters : PhaseParameters) (moment : ℕ)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) :
    fullKernelMoment parameters moment
        (fullKernelNegativeIdentityInverse parameters kernel low lowBound lowSmall) ≤
      fullKernelMoment parameters moment
          (fullIdentityKernel parameters dimension) +
        fullKernelNeumannConstant moment low *
          fullKernelMoment parameters moment kernel := by
  unfold fullKernelNegativeIdentityInverse
  exact (fullKernelNeg_moment_le parameters moment
    (fullKernelNeumannSum parameters kernel low lowBound lowSmall)).trans
      (fullKernelNeumannSum_moment_le parameters moment kernel low lowBound lowSmall)

/-- The exact full-kernel inverse has the manuscript one-high action bound;
the identity contribution and the positive-moment perturbation contribution
remain separated. -/
theorem fullKernelNegativeIdentityInverse_oneHigh_bound {dimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1)
    (high : NegativeTotalTrace parameters grade dimension)
    (lowField : NegativeTotalTrace parameters 0 dimension) :
    ‖fullOneHighKernelAction parameters grade
        (fullKernelNegativeIdentityInverse parameters kernel low lowBound lowSmall)
        high lowField‖ ≤
      2 ^ grade *
        ((fullKernelMoment parameters 1
              (fullIdentityKernel parameters dimension) +
            fullKernelNeumannConstant 1 low *
              fullKernelMoment parameters 1 kernel) * ‖high‖ +
          (fullKernelMoment parameters (grade + 1)
              (fullIdentityKernel parameters dimension) +
            fullKernelNeumannConstant (grade + 1) low *
              fullKernelMoment parameters (grade + 1) kernel) * ‖lowField‖) := by
  apply (fullOneHighKernelAction_bound parameters grade
    (fullKernelNegativeIdentityInverse parameters kernel low lowBound lowSmall)
    high lowField).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add
    (mul_le_mul_of_nonneg_right
      (fullKernelNegativeIdentityInverse_moment_le parameters 1 kernel low
        lowBound lowSmall) (norm_nonneg high))
    (mul_le_mul_of_nonneg_right
      (fullKernelNegativeIdentityInverse_moment_le parameters (grade + 1) kernel low
        lowBound lowSmall) (norm_nonneg lowField))

end Grad.BoundaryKernelAction
