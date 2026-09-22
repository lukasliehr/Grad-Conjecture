import ARW6ActualCartesianRows
import ARW7RadialMeasure

noncomputable section
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualRadialWords
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.ActualOuterCollar Grad.CollarCartesian Grad.BoundaryLift

def actualPolarOrderEnergy (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2) (order : ℕ) : ℝ :=
  productWordCoefficientSum order * ∑ word : CartesianWord order, ‖productWordCoefficient word‖ *
    ∑ mode ∈ finiteHighModes modes, |(mode : ℝ)| ^ (2 * wordCount word 1) *
      actualRadialCountEnergy parameter source mode (wordCount word 0)

def actualPolarRadialEnergy (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2) (grade : ℕ) : ℝ :=
  (2 * Real.pi) * ∑ order ∈ Finset.range (grade + 1), actualPolarOrderEnergy modes parameter source order

theorem actualPolarOrderEnergy_nonnegative (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2) (order : ℕ) :
    0 ≤ actualPolarOrderEnergy modes parameter source order := by
  apply mul_nonneg (productWordCoefficientSum_nonnegative _)
  apply Finset.sum_nonneg
  intro word _
  apply mul_nonneg (norm_nonneg _)
  exact Finset.sum_nonneg (fun mode _ => mul_nonneg (pow_nonneg (abs_nonneg _) _)
    (actualRadialCountEnergy_nonnegative parameter source mode _))

theorem actualMixedRowDensity_integral (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2)
    (core : ClosedJet 1) (same : source.val = closedL2Core core) (order : ℕ) :
    (∫ time in (0 : ℝ)..(1 / 2 : ℝ), mixedRowDensity (finiteHighModes modes) (actualWordRows parameter source) order time) ≤
      2 * actualPolarOrderEnergy modes parameter source order := by
  have rowContinuous (word : CartesianWord order) (mode : ℤ) : ContinuousOn
      (fun time => ‖actualWordRows parameter source order word mode time‖ ^ 2) (Icc (0 : ℝ) (1 / 2)) :=
    (actualWordRows_continuousOn parameter source core same order word mode).norm.pow 2
  have wordContinuous (word : CartesianWord order) : ContinuousOn
      (fun time => ‖productWordCoefficient word‖ * ∑ mode ∈ finiteHighModes modes,
        ‖actualWordRows parameter source order word mode time‖ ^ 2) (Icc (0 : ℝ) (1 / 2)) :=
    continuousOn_const.mul (continuousOn_finsetSum _ (fun mode _ => rowContinuous word mode))
  unfold mixedRowDensity
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun word _ => ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (wordContinuous word))]
  have wordIntegral (word : CartesianWord order) :
      (∫ time in (0 : ℝ)..(1 / 2 : ℝ), ‖productWordCoefficient word‖ * ∑ mode ∈ finiteHighModes modes,
        ‖actualWordRows parameter source order word mode time‖ ^ 2) ≤
        2 * (‖productWordCoefficient word‖ * ∑ mode ∈ finiteHighModes modes,
          |(mode : ℝ)| ^ (2 * wordCount word 1) * actualRadialCountEnergy parameter source mode (wordCount word 0)) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun mode _ => ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (rowContinuous word mode))]
    have comparison := Finset.sum_le_sum (s := finiteHighModes modes) (fun mode member =>
      actualWordRows_radial_integral parameter source core same mode (Finset.mem_filter.mp member).2 order word)
    exact (mul_le_mul_of_nonneg_left comparison (norm_nonneg _)).trans_eq (by rw [← Finset.mul_sum]; ring)
  exact (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun word _ => wordIntegral word))
    (productWordCoefficientSum_nonnegative order)).trans_eq (by rw [← Finset.mul_sum]; unfold actualPolarOrderEnergy; ring)

theorem actualMixedRowsDensity_integral (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2)
    (core : ClosedJet 1) (same : source.val = closedL2Core core) (grade : ℕ) :
    (∫ time in (0 : ℝ)..(1 / 2 : ℝ),
      mixedRowsDensity (finiteHighModes modes) (actualWordRows parameter source) grade time) ≤
      2 * actualPolarRadialEnergy modes parameter source grade := by
  have orderContinuous (order : ℕ) : ContinuousOn
      (mixedRowDensity (finiteHighModes modes) (actualWordRows parameter source) order) (Icc (0 : ℝ) (1 / 2)) := by
    apply continuousOn_const.mul
    apply continuousOn_finsetSum
    intro word _
    apply continuousOn_const.mul
    apply continuousOn_finsetSum
    intro mode _
    exact (actualWordRows_continuousOn parameter source core same order word mode).norm.pow 2
  unfold mixedRowsDensity
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun order _ => ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (orderContinuous order))]
  exact (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun order _ => actualMixedRowDensity_integral modes parameter source core same order))
    (by positivity : 0 ≤ 2 * Real.pi)).trans_eq (by rw [← Finset.mul_sum]; unfold actualPolarRadialEnergy; ring)

theorem actualOuterJet_radialEnergy_bound (index : CartesianMultiIndex) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2)
      (core : ClosedJet 1) (same : source.val = closedL2Core core),
      ‖closedDerivativeL2 index (actualOuterJet modes parameter source core same)‖ ^ 2 ≤
        constant * actualPolarRadialEnergy modes parameter source (cartesianOrder index) := by
  obtain ⟨constant, nonnegative, bound⟩ := actualOuterJet_mixedRows_bound index
  refine ⟨2 * constant, mul_nonneg (by norm_num) nonnegative, ?_⟩
  intro modes parameter source core same
  exact (bound modes parameter source core same).trans
    ((mul_le_mul_of_nonneg_left (actualMixedRowsDensity_integral modes parameter source core same _) nonnegative).trans_eq (by ring))

end Grad.ActualRadialWords
