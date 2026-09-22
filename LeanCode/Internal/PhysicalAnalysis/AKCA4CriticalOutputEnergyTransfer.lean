import AKCA3InsertedCriticalRadialEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.OriginalCoreRealization
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.AnnularCurrentLow Grad.ActualPuncturedReconstruction

theorem criticalCurveEnergy_transfer {input output : ℕ} (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (row : DivisionRow input lower) (curves : SmoothLowPhysicalRow parameters lower positive row)
    (grade : ℕ) (weighted : DivisionRow input lower)
    (same : ∀ mode : ℤ × ℤ, weighted mode = ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) • row mode)
    (outputCurve : ℝ → CellL2 output) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (estimate : ∀ radius, radius ∈ Icc lower 1 → ‖outputCurve radius‖ ≤ constant * ‖curves.curve grade radius‖) :
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖radius ^ (-(3 / 2 : ℝ)) • outputCurve radius‖ ^ 2)) ≤
      ENNReal.ofReal ((constant * ‖weighted‖) ^ 2) := by
  calc
    _ ≤ ∫⁻ radius in Icc lower 1, ENNReal.ofReal (constant ^ 2) * physicalBulkSquare input lower weighted radius := by
      apply lintegral_mono_ae
      filter_upwards [insertedCurve_criticalNativeSquare parameters lower positive row curves grade weighted same,
        ae_restrict_mem measurableSet_Icc] with radius native inside
      have scaled : ‖radius ^ (-(3 / 2 : ℝ)) • outputCurve radius‖ ≤
          constant * ‖radius ^ (-(3 / 2 : ℝ)) • curves.curve grade radius‖ := by
        rw [norm_smul,norm_smul]
        exact (mul_le_mul_of_nonneg_left (estimate radius inside) (norm_nonneg _)).trans_eq (by ring)
      calc
        _ ≤ ENNReal.ofReal (constant ^ 2) * ENNReal.ofReal (‖radius ^ (-(3 / 2 : ℝ)) • curves.curve grade radius‖ ^ 2) := by
          rw [← ENNReal.ofReal_mul (sq_nonneg constant),← mul_pow]
          exact ENNReal.ofReal_le_ofReal ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg nonnegative (norm_nonneg _))).mpr scaled)
        _ ≤ _ := by gcongr
    _ = ENNReal.ofReal (constant ^ 2) * ∫⁻ radius in Icc lower 1, physicalBulkSquare input lower weighted radius :=
      lintegral_const_mul'' _ (physicalBulkSquare_measurable input lower weighted).aemeasurable
    _ = _ := by rw [physicalBulkSquare_integral,← ENNReal.ofReal_mul (sq_nonneg constant),mul_pow]

end Grad.OriginalCoreRealization
