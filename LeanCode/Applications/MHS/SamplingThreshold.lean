import SampledSmoothFamily

noncomputable section

open Set

namespace Grad.PhysicalFamily.SamplingThreshold

open Grad.MainTarget
open Grad.PhysicalFamily
open Grad.PhysicalFamily.IntegerSampling

/-- A single integer threshold places every reciprocal sample in the common
open epsilon interval. -/
theorem exists_samplingThreshold (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) :
    ∃ firstPeriod : ℕ, 1 ≤ firstPeriod ∧
      ∀ period : ℕ, firstPeriod ≤ period →
        sampledEpsilon period ∈
          Set.Ioo (-family.epsilonZero) family.epsilonZero := by
  obtain ⟨firstPeriod, threshold⟩ :=
    (exists_nat_gt (max 1 (1 / family.epsilonZero)) :
      ∃ firstPeriod : ℕ,
        max 1 (1 / family.epsilonZero) < (firstPeriod : ℝ))
  have one_lt_first : (1 : ℝ) < firstPeriod :=
    lt_of_le_of_lt (le_max_left 1 (1 / family.epsilonZero)) threshold
  have firstPositive : 1 ≤ firstPeriod := by
    exact_mod_cast (le_of_lt one_lt_first)
  refine ⟨firstPeriod, firstPositive, ?_⟩
  intro period periodAfter
  have first_le_period_real : (firstPeriod : ℝ) ≤ period := by
    exact_mod_cast periodAfter
  have reciprocalEpsilon_lt_period :
      1 / family.epsilonZero < (period : ℝ) :=
    (lt_of_le_of_lt (le_max_right 1 (1 / family.epsilonZero))
      threshold).trans_le first_le_period_real
  have periodPositiveNat : 0 < period :=
    lt_of_lt_of_le (Nat.zero_lt_of_lt firstPositive) periodAfter
  have periodPositive : (0 : ℝ) < period := by exact_mod_cast periodPositiveNat
  have sampledPositive : 0 < sampledEpsilon period := by
    exact inv_pos.mpr periodPositive
  refine ⟨lt_of_lt_of_le (neg_lt_zero.mpr family.epsilonPositive)
    sampledPositive.le, ?_⟩
  unfold sampledEpsilon
  rw [inv_lt_iff_one_lt_mul₀ periodPositive]
  have productBound : 1 < (period : ℝ) * family.epsilonZero :=
    (div_lt_iff₀ family.epsilonPositive).mp reciprocalEpsilon_lt_period
  simpa [mul_comm] using productBound

end Grad.PhysicalFamily.SamplingThreshold
