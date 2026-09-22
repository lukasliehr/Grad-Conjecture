import AKAW13SameCorrectedCurveNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.ActualNativeCellMoments
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.AnnularCurrentLow

theorem curveEnergy_transfer {input output : ℕ} (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (row : DivisionRow input lower) (curves : SmoothLowPhysicalRow parameters lower positive row)
    (grade : ℕ) (weighted : DivisionRow input lower)
    (same : ∀ mode : ℤ × ℤ, weighted mode = ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) • row mode)
    (outputCurve : ℝ → CellL2 output) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (estimate : ∀ radius, radius ∈ Icc lower 1 → ‖outputCurve radius‖ ≤ constant * ‖curves.curve grade radius‖) :
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖outputCurve radius‖ ^ 2)) ≤
      ENNReal.ofReal ((constant * ‖weighted‖) ^ 2) := by
  calc
    _ ≤ ∫⁻ radius in Icc lower 1, ENNReal.ofReal (constant ^ 2) * ENNReal.ofReal (‖curves.curve grade radius‖ ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
      rw [← ENNReal.ofReal_mul (sq_nonneg constant),← mul_pow]
      exact ENNReal.ofReal_le_ofReal ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg nonnegative (norm_nonneg _))).mpr (estimate radius inside))
    _ = ENNReal.ofReal (constant ^ 2) * ∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖curves.curve grade radius‖ ^ 2) :=
      lintegral_const_mul'' _ (((curves.smooth grade).continuousOn.aestronglyMeasurable measurableSet_Icc).norm.pow 2).aemeasurable.ennreal_ofReal
    _ ≤ ENNReal.ofReal (constant ^ 2) * ENNReal.ofReal (‖weighted‖ ^ 2) :=
      by
        gcongr
        exact insertedCurve_collarEnergy parameters lower positive row curves grade weighted same
    _ = _ := by rw [← ENNReal.ofReal_mul (sq_nonneg constant),mul_pow]

end Grad.ActualNativeCellMoments
