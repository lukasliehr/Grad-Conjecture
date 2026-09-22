import ARW9OrdinaryOuterEnergy
import AOD9ActualMixedRadialConsumer

set_option maxHeartbeats 2000000

noncomputable section
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualRadialWords
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.ActualOuterCollar Grad.ClosedDiskRegularity Grad.CollarCartesian Grad.BoundaryLift
open Grad.GaugeCoefficients.Algebra Grad.OrdinaryDiskCalculus
attribute [local instance] unitNormedSpace

def polarRowGeometryConstant (grade : ℕ) : ℝ :=
  (2 * Real.pi) * ∑ order ∈ Finset.range (grade + 1), productWordCoefficientSum order ^ 2

theorem polarRowGeometryConstant_nonnegative (grade : ℕ) : 0 ≤ polarRowGeometryConstant grade := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem actualPolarRadialEnergy_source_bound (grade : ℕ) (ceiling : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ parameter : ℝ, |parameter| ≤ ceiling →
      ∀ (source : highDiskL2) (core : ClosedJet 1), source.val = closedL2Core core →
      ∀ modes : Finset ℤ, actualPolarRadialEnergy modes parameter source (grade + 2) ≤
        constant * ‖unitDiskCoreInto grade core‖ ^ 2 := by
  obtain ⟨constant, nonnegative, bound⟩ := actualAllMixedRadial_finite grade
    (1 / 2) (by norm_num) (by norm_num) ceiling
  refine ⟨polarRowGeometryConstant (grade + 2) * constant,
    mul_nonneg (polarRowGeometryConstant_nonnegative _) nonnegative, ?_⟩
  intro parameter parameterBound source core same modes
  have wordBound (order : ℕ) (upper : order ≤ grade + 2) (word : CartesianWord order) :
      (∑ mode ∈ finiteHighModes modes, |(mode : ℝ)| ^ (2 * wordCount word 1) *
        actualRadialCountEnergy parameter source mode (wordCount word 0)) ≤ constant * ‖unitDiskCoreInto grade core‖ ^ 2 := by
    have literal :
        (∑ mode ∈ finiteHighModes modes, |(mode : ℝ)| ^ (2 * wordCount word 1) *
          actualRadialCountEnergy parameter source mode (wordCount word 0)) =
        ∑ mode ∈ finiteHighModes modes, highRadialDerivativeEnergy (1 / 2) (by norm_num) (by norm_num)
          parameter source (wordCount word 0) (wordCount word 1) mode := by
      apply Finset.sum_congr rfl
      intro mode member
      exact (highRadialDerivativeEnergy_literal (1 / 2) (by norm_num) (by norm_num)
        parameter source (wordCount word 0) (wordCount word 1) mode (Finset.mem_filter.mp member).2).symm
    rw [literal]
    exact bound parameter parameterBound source core same _ _ ((wordCount_total word).trans_le upper) _
  have orderBound (order : ℕ) (upper : order ≤ grade + 2) :
      actualPolarOrderEnergy modes parameter source order ≤
        productWordCoefficientSum order ^ 2 * constant * ‖unitDiskCoreInto grade core‖ ^ 2 := by
    unfold actualPolarOrderEnergy
    calc
      _ ≤ productWordCoefficientSum order * ∑ word : CartesianWord order,
          ‖productWordCoefficient word‖ * (constant * ‖unitDiskCoreInto grade core‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (productWordCoefficientSum_nonnegative order)
        exact Finset.sum_le_sum (fun word _ => mul_le_mul_of_nonneg_left
          (wordBound order upper word) (norm_nonneg (productWordCoefficient word)))
      _ = _ := by rw [← Finset.sum_mul]; unfold productWordCoefficientSum; ring
  unfold actualPolarRadialEnergy
  calc
    _ ≤ (2 * Real.pi) * ∑ order ∈ Finset.range (grade + 2 + 1),
        productWordCoefficientSum order ^ 2 * constant * ‖unitDiskCoreInto grade core‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * Real.pi)
      exact Finset.sum_le_sum (fun order member =>
        orderBound order (by have := Finset.mem_range.mp member; omega))
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; unfold polarRowGeometryConstant; ring

/-- Actual finite outer H^(s+2) gain, on one parameter interval and uniformly
in angular cutoff, from the original ordinary Hs source norm. -/
theorem finiteOuterWithinOrdinary_gain_sq (grade : ℕ) (ceiling : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ parameter : ℝ, |parameter| ≤ ceiling →
      ∀ (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core) (modes : Finset ℤ),
      ‖withinOrdinaryDisk (grade + 2) (finiteOuterField modes parameter source)
        (finiteOuterField_smooth modes parameter source core same)‖ ^ 2 ≤
        constant * ‖unitDiskCoreInto grade core‖ ^ 2 := by
  obtain ⟨outerConstant, outerNonnegative, outerBound⟩ := finiteOuterWithinOrdinary_radial_bound (grade + 2)
  obtain ⟨radialConstant, radialNonnegative, radialBound⟩ := actualPolarRadialEnergy_source_bound grade ceiling
  refine ⟨outerConstant * radialConstant, mul_nonneg outerNonnegative radialNonnegative, ?_⟩
  intro parameter parameterBound source core same modes
  exact (outerBound modes parameter source core same).trans
    ((mul_le_mul_of_nonneg_left (radialBound parameter parameterBound source core same modes) outerNonnegative).trans_eq (by ring))

theorem finiteOuterWithinOrdinary_gain (grade : ℕ) (ceiling : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ parameter : ℝ, |parameter| ≤ ceiling →
      ∀ (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core) (modes : Finset ℤ),
      ‖withinOrdinaryDisk (grade + 2) (finiteOuterField modes parameter source)
        (finiteOuterField_smooth modes parameter source core same)‖ ≤
        constant * ‖unitDiskCoreInto grade core‖ := by
  obtain ⟨constant, nonnegative, bound⟩ := finiteOuterWithinOrdinary_gain_sq grade ceiling
  refine ⟨Real.sqrt constant, Real.sqrt_nonneg _, ?_⟩
  intro parameter parameterBound source core same modes
  have estimate := bound parameter parameterBound source core same modes
  have squared : ‖withinOrdinaryDisk (grade + 2) (finiteOuterField modes parameter source)
      (finiteOuterField_smooth modes parameter source core same)‖ ^ 2 ≤
      (Real.sqrt constant * ‖unitDiskCoreInto grade core‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt nonnegative]
    exact estimate
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp squared

end Grad.ActualRadialWords
