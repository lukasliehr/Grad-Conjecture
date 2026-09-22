import SamplingThreshold

noncomputable section

open Set

namespace Grad.PhysicalFamily.GeometricSamplingThreshold

open Grad.PhysicalFamily
open Grad.PhysicalFamily.IntegerSampling

/-- One integer threshold simultaneously enters the analytic epsilon interval,
makes the stored physical C² error smaller than an arbitrary positive margin,
and makes the sampled major radius exceed an arbitrary prescribed floor. -/
theorem exists_geometricSamplingThreshold
    (cellLength : ℝ) (cellLengthPositive : 0 < cellLength)
    (family : CellSolutionFamily cellLength)
    (margin : ℝ) (marginPositive : 0 < margin) (radiusFloor : ℝ) :
    ∃ firstPeriod : ℕ, 1 ≤ firstPeriod ∧
      ∀ period : ℕ, firstPeriod ≤ period →
        sampledEpsilon period ∈
            Set.Ioo (-family.epsilonZero) family.epsilonZero ∧
          family.bound * |sampledEpsilon period| < margin ∧
          radiusFloor < (period : ℝ) * cellLength := by
  obtain ⟨firstPeriod, threshold⟩ :=
    (exists_nat_gt
      (max 1
        (max (1 / family.epsilonZero)
          (max (family.bound / margin) (radiusFloor / cellLength)))) :
      ∃ firstPeriod : ℕ,
        max 1
            (max (1 / family.epsilonZero)
              (max (family.bound / margin) (radiusFloor / cellLength))) <
          (firstPeriod : ℝ))
  have one_lt_first : (1 : ℝ) < firstPeriod :=
    lt_of_le_of_lt (le_max_left 1 _) threshold
  have firstPositive : 1 ≤ firstPeriod := by
    exact_mod_cast (le_of_lt one_lt_first)
  refine ⟨firstPeriod, firstPositive, ?_⟩
  intro period periodAfter
  have first_le_period_real : (firstPeriod : ℝ) ≤ period := by
    exact_mod_cast periodAfter
  have fullThreshold :
      max 1
          (max (1 / family.epsilonZero)
            (max (family.bound / margin) (radiusFloor / cellLength))) <
        (period : ℝ) :=
    threshold.trans_le first_le_period_real
  have periodPositiveNat : 0 < period :=
    lt_of_lt_of_le (Nat.zero_lt_of_lt firstPositive) periodAfter
  have periodPositive : (0 : ℝ) < period := by
    exact_mod_cast periodPositiveNat
  have sampledPositive : 0 < sampledEpsilon period :=
    inv_pos.mpr periodPositive
  have epsilonThreshold : 1 / family.epsilonZero < (period : ℝ) :=
    (le_max_left (1 / family.epsilonZero)
      (max (family.bound / margin) (radiusFloor / cellLength))).trans_lt
      ((le_max_right 1 _).trans_lt fullThreshold)
  have epsilonUpper : sampledEpsilon period < family.epsilonZero := by
    unfold sampledEpsilon
    rw [inv_lt_iff_one_lt_mul₀ periodPositive]
    have productBound : 1 < (period : ℝ) * family.epsilonZero :=
      (div_lt_iff₀ family.epsilonPositive).mp epsilonThreshold
    simpa [mul_comm] using productBound
  have errorThreshold : family.bound / margin < (period : ℝ) :=
    (le_max_left (family.bound / margin) (radiusFloor / cellLength)).trans_lt
      ((le_max_right (1 / family.epsilonZero) _).trans_lt
        ((le_max_right 1 _).trans_lt fullThreshold))
  have errorSmall :
      family.bound * |sampledEpsilon period| < margin := by
    rw [abs_of_pos sampledPositive]
    unfold sampledEpsilon
    rw [← div_eq_mul_inv]
    apply (div_lt_iff₀ periodPositive).2
    have numeratorBound : family.bound < margin * (period : ℝ) := by
      simpa [mul_comm] using
        (div_lt_iff₀ marginPositive).mp errorThreshold
    simpa [mul_comm] using numeratorBound
  have radiusThreshold : radiusFloor / cellLength < (period : ℝ) :=
    (le_max_right (family.bound / margin) (radiusFloor / cellLength)).trans_lt
      ((le_max_right (1 / family.epsilonZero) _).trans_lt
        ((le_max_right 1 _).trans_lt fullThreshold))
  have radiusLarge : radiusFloor < (period : ℝ) * cellLength := by
    exact (div_lt_iff₀ cellLengthPositive).mp radiusThreshold
  exact
    ⟨⟨lt_of_lt_of_le (neg_lt_zero.mpr family.epsilonPositive)
        sampledPositive.le, epsilonUpper⟩,
      errorSmall, radiusLarge⟩

end Grad.PhysicalFamily.GeometricSamplingThreshold
