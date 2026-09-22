import ARC7CartesianRowEnergy

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.CollarCartesian
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.BoundaryLift

theorem finiteProfileRowDensity_continuous {dimension : ℕ} (modes : Finset ℤ)
    (profiles : ℤ → ℝ → ComplexEuclidean dimension) (smooth : ∀ mode, ContDiff ℝ ∞ (profiles mode))
    (order : ℕ) : Continuous (finiteProfileRowDensity modes profiles order) := by
  apply continuous_const.mul
  apply continuous_finsetSum
  intro word _
  apply continuous_const.mul
  apply continuous_finsetSum
  intro mode _
  exact (((tensorWord_continuous _ (profileMode_smooth mode (profiles mode) (smooth mode)) word).comp
    (continuous_id.prodMk continuous_const)).norm).pow 2

theorem finiteProfileField_radial_integral {dimension : ℕ} (modes : Finset ℤ)
    (profiles : ℤ → ℝ → ComplexEuclidean dimension) (smooth : ∀ mode, ContDiff ℝ ∞ (profiles mode))
    (order : ℕ) :
    halfCollarIntegral (fun point =>
      ‖iteratedFDeriv ℝ order (finiteProfileField modes profiles) point‖ ^ 2) ≤
      (2 * Real.pi) * ∫ time in (0 : ℝ)..(1 / 2 : ℝ), finiteProfileRowDensity modes profiles order time := by
  have tensorContinuous : Continuous (fun point : ℝ × ℝ =>
      ‖iteratedFDeriv ℝ order (finiteProfileField modes profiles) point‖ ^ 2) :=
    (((finiteProfileField_smooth modes profiles smooth).continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm).pow 2
  have angularIntegralContinuous : Continuous (fun time : ℝ => ∫ angle in -Real.pi..Real.pi,
      ‖iteratedFDeriv ℝ order (finiteProfileField modes profiles) (time, angle)‖ ^ 2) :=
    timeIntegral_continuous _ (tensorContinuous.comp continuous_swap)
      (-Real.pi) Real.pi (neg_le_self Real.pi_pos.le)
  have comparison := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (angularIntegralContinuous.intervalIntegrable _ _)
    ((continuous_const.mul (finiteProfileRowDensity_continuous modes profiles smooth order)).intervalIntegrable _ _)
    (fun time _ => finiteProfileField_tensor_integral modes profiles smooth order time)
  simp only [Pi.mul_apply] at comparison
  rw [halfCollarIntegral_swap _ tensorContinuous, intervalIntegral.integral_const_mul] at comparison
  exact comparison

/-- All mixed radial/angular rows, with no mode-count or frequency-loss factor. -/
def finiteProfileEnergy {dimension : ℕ} (modes : Finset ℤ)
    (profiles : ℤ → ℝ → ComplexEuclidean dimension) (grade : ℕ) : ℝ :=
  (2 * Real.pi) * ∑ order ∈ Finset.range (grade + 1),
    ∫ time in (0 : ℝ)..(1 / 2 : ℝ), finiteProfileRowDensity modes profiles order time

theorem finiteProfileField_density_energy {dimension : ℕ} (modes : Finset ℤ)
    (profiles : ℤ → ℝ → ComplexEuclidean dimension) (smooth : ∀ mode, ContDiff ℝ ∞ (profiles mode))
    (grade : ℕ) :
    halfCollarIntegral (polarJetSquaredDensity (finiteProfileField modes profiles) grade) ≤
      finiteProfileEnergy modes profiles grade := by
  have derivativeContinuous (order : ℕ) : Continuous (fun point : ℝ × ℝ =>
      ‖iteratedFDeriv ℝ order (finiteProfileField modes profiles) point‖ ^ 2) :=
    (((finiteProfileField_smooth modes profiles smooth).continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm).pow 2
  rw [show polarJetSquaredDensity (finiteProfileField modes profiles) grade =
      fun point => ∑ order ∈ Finset.range (grade + 1),
        ‖iteratedFDeriv ℝ order (finiteProfileField modes profiles) point‖ ^ 2 by rfl,
    halfCollarIntegral_finsetSum _ _ (fun order _ => derivativeContinuous order),
    finiteProfileEnergy, Finset.mul_sum]
  exact Finset.sum_le_sum (fun order _ => finiteProfileField_radial_integral modes profiles smooth order)

end Grad.CollarCartesian
