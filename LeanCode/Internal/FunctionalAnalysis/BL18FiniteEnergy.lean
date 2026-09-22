import BL17PolarEnergy

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

def polarEnergyConstant (parameters : PhaseParameters) (order : ℕ) : ℝ :=
  ((2 * Real.pi) * productWordCoefficientSum order ^ 2) *
    (polarDerivativeConstant order parameters.gamma ^ 2 / (2 * boundaryDecayRate parameters))

theorem polarEnergyConstant_nonnegative (parameters : PhaseParameters) (order : ℕ) :
    0 ≤ polarEnergyConstant parameters order := by
  have decayPositive := boundaryDecayRate_pos parameters
  unfold polarEnergyConstant
  positivity

theorem finitePolarField_radial_integral {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (modes : Finset ℤ) (values : ℤ → ComplexEuclidean dimension) (order : ℕ) :
    collarIntegral (fun point =>
      ‖iteratedFDeriv ℝ order (finitePolarField parameters cell modes values) point‖ ^ 2) ≤
      ((2 * Real.pi) * productWordCoefficientSum order ^ 2) * ∑ mode ∈ modes,
        ∫ time in (0 : ℝ)..(1 / 4 : ℝ),
          ‖iteratedFDeriv ℝ order (polarModeField parameters (mode, cell) (values mode)) (time, 0)‖ ^ 2 := by
  have tensorContinuous : Continuous (fun point : ℝ × ℝ =>
      ‖iteratedFDeriv ℝ order (finitePolarField parameters cell modes values) point‖ ^ 2) :=
    (((finitePolarField_smooth parameters cell modes values).continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm).pow 2
  have angularIntegralContinuous : Continuous (fun time : ℝ => ∫ angle in -Real.pi..Real.pi,
      ‖iteratedFDeriv ℝ order (finitePolarField parameters cell modes values) (time, angle)‖ ^ 2) :=
    timeIntegral_continuous _ (tensorContinuous.comp continuous_swap)
      (-Real.pi) Real.pi (neg_le_self Real.pi_pos.le)
  have modeContinuous (mode : ℤ) : Continuous (fun time : ℝ =>
      ‖iteratedFDeriv ℝ order (polarModeField parameters (mode, cell) (values mode)) (time, 0)‖ ^ 2) :=
    ((((polarModeField_smooth parameters (mode, cell) (values mode)).continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).comp
      (continuous_id.prodMk continuous_const)).norm).pow 2
  have rightContinuous : Continuous (fun time : ℝ =>
      ((2 * Real.pi) * productWordCoefficientSum order ^ 2) * ∑ mode ∈ modes,
        ‖iteratedFDeriv ℝ order (polarModeField parameters (mode, cell) (values mode)) (time, 0)‖ ^ 2) :=
    continuous_const.mul (continuous_finsetSum modes (fun mode _ => modeContinuous mode))
  have comparison := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (angularIntegralContinuous.intervalIntegrable _ _) (rightContinuous.intervalIntegrable _ _)
    (fun time _ => finitePolarField_tensor_integral parameters cell modes values order time)
  rw [collarIntegral_swap _ tensorContinuous, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun mode _ => (modeContinuous mode).intervalIntegrable _ _)] at comparison
  exact comparison

theorem finitePolarField_weighted_energy {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (modes : Finset ℤ) (values : ℤ → ComplexEuclidean dimension) (grade order : ℕ)
    (gradePositive : 1 ≤ grade) (orderBound : order ≤ grade) :
    cellFrequency cell ^ (2 * (grade - order)) * collarIntegral (fun point =>
      ‖iteratedFDeriv ℝ order (finitePolarField parameters cell modes values) point‖ ^ 2) ≤
      polarEnergyConstant parameters order * ∑ mode ∈ modes,
        boundaryFrequency (mode, cell) ^ (2 * grade - 1) * ‖values mode‖ ^ 2 := by
  have comparison := mul_le_mul_of_nonneg_left
    (finitePolarField_radial_integral parameters cell modes values order)
    (pow_nonneg (cellFrequency_pos cell).le (2 * (grade - order)))
  apply comparison.trans
  calc
    _ = ((2 * Real.pi) * productWordCoefficientSum order ^ 2) * ∑ mode ∈ modes,
        cellFrequency cell ^ (2 * (grade - order)) *
          ∫ time in (0 : ℝ)..(1 / 4 : ℝ),
            ‖iteratedFDeriv ℝ order (polarModeField parameters (mode, cell) (values mode)) (time, 0)‖ ^ 2 := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ ((2 * Real.pi) * productWordCoefficientSum order ^ 2) * ∑ mode ∈ modes,
        (polarDerivativeConstant order parameters.gamma ^ 2 / (2 * boundaryDecayRate parameters)) *
          boundaryFrequency (mode, cell) ^ (2 * grade - 1) * ‖values mode‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro mode _
      exact polarModeField_weighted_energy parameters (mode, cell) (values mode) grade order gradePositive orderBound
    _ = _ := by
      simp only [polarEnergyConstant, mul_assoc, Finset.mul_sum]

end Grad.BoundaryLift
