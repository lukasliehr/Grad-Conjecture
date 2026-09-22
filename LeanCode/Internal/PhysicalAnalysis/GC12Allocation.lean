import GC12Majorant

noncomputable section

open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann.Regularity

/-- Number of factors hit by a labelled derivative allocation. -/
def allocationHitCount {derivatives factors : ℕ}
    (allocation : Fin derivatives → Fin factors) : ℕ :=
  (Finset.univ.image allocation).card

theorem allocationHitCount_le_derivatives {derivatives factors : ℕ}
    (allocation : Fin derivatives → Fin factors) :
    allocationHitCount allocation ≤ derivatives := by
  unfold allocationHitCount
  calc
    (Finset.univ.image allocation).card ≤ Finset.univ.card :=
      Finset.card_image_le
    _ = derivatives := Fintype.card_fin derivatives

theorem allocationHitCount_le_factors {derivatives factors : ℕ}
    (allocation : Fin derivatives → Fin factors) :
    allocationHitCount allocation ≤ factors := by
  unfold allocationHitCount
  calc
    (Finset.univ.image allocation).card ≤
        (Finset.univ : Finset (Fin factors)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = factors := Fintype.card_fin factors

/-- One labelled allocation has at most `grade` non-base factors.  All
remaining factors retain the base contraction, with no iterated graded
product constant. -/
theorem allocation_product_le_ap13 {grade derivatives factors : ℕ}
    (allocation : Fin derivatives → Fin factors)
    {theta thetaStar high : ℝ}
    (derivativesLe : derivatives ≤ grade)
    (thetaNonnegative : 0 ≤ theta) (thetaLeStar : theta ≤ thetaStar)
    (thetaStarLt : thetaStar < 1) (highNonnegative : 0 ≤ high) :
    high ^ allocationHitCount allocation *
        theta ^ (factors - allocationHitCount allocation) ≤
      thetaStar ^ (factors - grade) * (1 + high) ^ grade := by
  let hits := allocationHitCount allocation
  have hitsLeGrade : hits ≤ grade :=
    (allocationHitCount_le_derivatives allocation).trans derivativesLe
  have hitsLeFactors : hits ≤ factors :=
    allocationHitCount_le_factors allocation
  have thetaStarNonnegative : 0 ≤ thetaStar := thetaNonnegative.trans thetaLeStar
  have thetaStarLeOne : thetaStar ≤ 1 := thetaStarLt.le
  have highLe : high ≤ 1 + high := by linarith
  have highPowerLe : high ^ hits ≤ (1 + high) ^ grade := by
    calc
      high ^ hits ≤ (1 + high) ^ hits := by gcongr
      _ ≤ (1 + high) ^ grade :=
        pow_le_pow_right₀ (by linarith) hitsLeGrade
  by_cases gradeLeFactors : grade ≤ factors
  · have thetaPowerLe : theta ^ (factors - hits) ≤
        thetaStar ^ (factors - grade) := by
      calc
        theta ^ (factors - hits) ≤ thetaStar ^ (factors - hits) := by gcongr
        _ = thetaStar ^ (factors - grade) * thetaStar ^ (grade - hits) := by
          rw [← pow_add]
          congr 1
          omega
        _ ≤ thetaStar ^ (factors - grade) * 1 := by
          gcongr
          exact pow_le_one₀ thetaStarNonnegative thetaStarLeOne
        _ = thetaStar ^ (factors - grade) := mul_one _
    calc
      high ^ hits * theta ^ (factors - hits) ≤
          (1 + high) ^ grade * thetaStar ^ (factors - grade) :=
        mul_le_mul highPowerLe thetaPowerLe
          (pow_nonneg thetaNonnegative _)
          (pow_nonneg (by linarith : 0 ≤ 1 + high) _)
      _ = thetaStar ^ (factors - grade) * (1 + high) ^ grade := by
        rw [mul_comm]
  · have factorsLtGrade : factors < grade := Nat.lt_of_not_ge gradeLeFactors
    have thetaPowerLeOne : theta ^ (factors - hits) ≤ 1 :=
      pow_le_one₀ thetaNonnegative (thetaLeStar.trans thetaStarLeOne)
    rw [Nat.sub_eq_zero_of_le factorsLtGrade.le, pow_zero, one_mul]
    exact (mul_le_mul highPowerLe thetaPowerLeOne
      (pow_nonneg thetaNonnegative _)
      (pow_nonneg (by linarith : 0 ≤ 1 + high) _)).trans_eq (mul_one _)

/-- Summing all assignments of the labelled derivative positions contributes
at most the exact polynomial factor `factors^grade`. -/
theorem allocation_sum_le_ap13 {grade derivatives factors : ℕ}
    (positiveFactors : 0 < factors) (derivativesLe : derivatives ≤ grade)
    {theta thetaStar high : ℝ}
    (thetaNonnegative : 0 ≤ theta) (thetaLeStar : theta ≤ thetaStar)
    (thetaStarLt : thetaStar < 1) (highNonnegative : 0 ≤ high) :
    (∑ allocation : Fin derivatives → Fin factors,
      high ^ allocationHitCount allocation *
        theta ^ (factors - allocationHitCount allocation)) ≤
      (factors : ℝ) ^ grade *
        (thetaStar ^ (factors - grade) * (1 + high) ^ grade) := by
  calc
    (∑ allocation : Fin derivatives → Fin factors,
        high ^ allocationHitCount allocation *
          theta ^ (factors - allocationHitCount allocation)) ≤
      ∑ _allocation : Fin derivatives → Fin factors,
        thetaStar ^ (factors - grade) * (1 + high) ^ grade := by
      exact Finset.sum_le_sum fun allocation _membership =>
        allocation_product_le_ap13 allocation derivativesLe thetaNonnegative
          thetaLeStar thetaStarLt highNonnegative
    _ = (factors : ℝ) ^ derivatives *
        (thetaStar ^ (factors - grade) * (1 + high) ^ grade) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
      norm_cast
    _ ≤ (factors : ℝ) ^ grade *
        (thetaStar ^ (factors - grade) * (1 + high) ^ grade) := by
      have oneLeFactors : 1 ≤ factors := positiveFactors
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by exact_mod_cast oneLeFactors) derivativesLe)
        (mul_nonneg
          (pow_nonneg (thetaNonnegative.trans thetaLeStar) _)
          (pow_nonneg (by linarith : 0 ≤ 1 + high) _))

end Grad.GaugeCoefficients.Neumann.Regularity
