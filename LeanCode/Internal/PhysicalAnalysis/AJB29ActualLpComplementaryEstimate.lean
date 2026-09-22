import AJB28OriginalFrequencyOneHighAllocation
import AJB27OriginalLowGradeNormBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.AnnularOrbitGenerators
open Grad.CartesianState Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularFluxTrace

theorem lp_frequency_generator_bound {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (frequency : ι → ℝ) (mode : ι → ℤ) (frequencyNonnegative : ∀ index, 0 ≤ frequency index)
    (modeBound : ∀ index, |(mode index : ℝ)| ≤ frequency index)
    (field weighted generator : lp (fun _ : ι => V) 2) (order : ℕ)
    (weightedActual : ∀ index, weighted index = ((frequency index ^ order : ℝ) : ℂ) • field index)
    (generatorActual : ∀ index, generator index = (Complex.I * (mode index : ℂ)) ^ order • field index) :
    ‖generator‖ ≤ ‖weighted‖ := by
  apply lp.norm_mono (by norm_num)
  intro index
  rw [generatorActual, weightedActual, norm_smul, norm_smul, Grad.AnnularLowOrbit.cellGeneratorFactor_norm,
    Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (frequencyNonnegative index) order)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (modeBound index) order) (norm_nonneg _)

/-- The original coefficient budget and complementary Fourier derivative are
paired before summing. The high data norm and high state norm never multiply. -/
theorem lp_complementary_oneHigh {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (parameters : PhaseParameters) (base : ACore parameters 3) (rho epsilon : ℝ)
    (frequency : ι → ℝ) (mode : ι → ℤ) (frequencyPositive : ∀ index, 0 < frequency index)
    (modeBound : ∀ index, |(mode index : ℝ)| ≤ frequency index)
    (field weighted generator : lp (fun _ : ι => V) 2)
    (offset grade order : ℕ) (gradePositive : 0 < grade) (ordered : order ≤ grade)
    (weightedActual : ∀ index, weighted index = ((frequency index ^ grade : ℝ) : ℂ) • field index)
    (generatorActual : ∀ index, generator index = (Complex.I * (mode index : ℂ)) ^ (grade - order) • field index) :
    physicalBudget parameters base rho epsilon (offset + order) * ‖generator‖ ≤
      physicalInterpolationConstant offset grade *
        (physicalBudget parameters base rho epsilon offset * ‖weighted‖ +
          physicalBudget parameters base rho epsilon (offset + grade) * ‖field‖) := by
  let middle := physicalBudget parameters base rho epsilon (offset + order)
  let low := physicalBudget parameters base rho epsilon offset
  let high := physicalBudget parameters base rho epsilon (offset + grade)
  let constant := physicalInterpolationConstant offset grade
  have middleNonnegative : 0 ≤ middle := physicalBudget_nonnegative _ _ _ _ _
  have lowNonnegative : 0 ≤ low := physicalBudget_nonnegative _ _ _ _ _
  have highNonnegative : 0 ≤ high := physicalBudget_nonnegative _ _ _ _ _
  have constantNonnegative : 0 ≤ constant := zero_le_one.trans (physicalInterpolationConstant_one_le offset grade)
  have pointwise : ‖middle • lpNormFamily generator‖ ≤
      ‖constant • (low • lpNormFamily weighted + high • lpNormFamily field)‖ := by
    apply lp.norm_mono (by norm_num)
    intro index
    change ‖middle • ‖generator index‖‖ ≤ ‖constant • (low • ‖weighted index‖ + high • ‖field index‖)‖
    rw [norm_smul, Real.norm_of_nonneg middleNonnegative, norm_norm,
      norm_smul, Real.norm_of_nonneg constantNonnegative]
    simp only [smul_eq_mul]
    rw [Real.norm_of_nonneg (add_nonneg (mul_nonneg lowNonnegative (norm_nonneg _))
      (mul_nonneg highNonnegative (norm_nonneg _)))]
    rw [generatorActual, norm_smul, Grad.AnnularLowOrbit.cellGeneratorFactor_norm,
      weightedActual, norm_smul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (frequencyPositive index).le grade)]
    have frequencyPower := pow_le_pow_left₀ (abs_nonneg (mode index : ℝ)) (modeBound index) (grade - order)
    have budgetSplit := physical_budget_frequency_split parameters base rho epsilon (frequency index)
      (frequencyPositive index) offset grade order gradePositive ordered
    have allocated := (mul_le_mul_of_nonneg_left frequencyPower middleNonnegative).trans budgetSplit
    calc
      _ = middle * |(mode index : ℝ)| ^ (grade - order) * ‖field index‖ := by ring
      _ ≤ physicalInterpolationConstant offset grade *
          (physicalBudget parameters base rho epsilon offset * frequency index ^ grade +
            physicalBudget parameters base rho epsilon (offset + grade)) * ‖field index‖ :=
        mul_le_mul_of_nonneg_right allocated (norm_nonneg (field index))
      _ = _ := by dsimp [low, high, constant]; ring
  rw [norm_smul, Real.norm_of_nonneg middleNonnegative, lpNormFamily_norm] at pointwise
  apply pointwise.trans
  rw [norm_smul, Real.norm_of_nonneg constantNonnegative]
  apply mul_le_mul_of_nonneg_left _ constantNonnegative
  have triangle := norm_add_le (low • lpNormFamily weighted) (high • lpNormFamily field)
  simpa only [norm_smul, Real.norm_of_nonneg lowNonnegative, Real.norm_of_nonneg highNonnegative, lpNormFamily_norm] using triangle

end Grad.AnnularOrbitGenerators
