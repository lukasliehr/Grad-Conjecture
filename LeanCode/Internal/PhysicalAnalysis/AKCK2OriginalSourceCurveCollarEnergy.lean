import AKCK1SameFullG3FourOrderPayment
import AKAW12InsertedCurveNativeEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.SourceCollarFullSource Grad.SourceCollarBulk
open Grad.ActualNativeCellMoments Grad.AnnularIncomingIntegrability Grad.AnnularCurrentLow
open Grad.ActualPuncturedReconstruction

/-- Original source row norms pay the SAME phase-weighted radial curve on
a fixed positive collar. The only conversion factor depends on that collar,
not on the source grade or coefficients. -/
theorem originalSourceCurve_collarEnergy {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (power : ℕ)
    (row : DivisionRow dimension lower) (curve : ℝ → CellL2 dimension)
    (same : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      curve radius mode = (annularFrequency mode.1 mode.2 : ℂ)^power •
        ((Real.exp (Grad.PhaseAlgebra.radialPhase parameters radius mode.2) : ℂ) •
          originalRowCoefficient parameters power lower row radius mode)) :
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖curve radius‖^2)) ≤
      ENNReal.ofReal ((lower⁻¹*‖row‖)^2) := by
  have point : ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      ENNReal.ofReal (‖curve radius‖^2) ≤ ENNReal.ofReal ((lower⁻¹)^2)*physicalBulkSquare dimension lower row radius := by
    filter_upwards [same,ae_restrict_mem measurableSet_Icc] with radius actual inside
    have radiusPositive := positive.trans_le inside.1
    have squareRoot := Real.sq_sqrt radiusPositive.le
    have radiusLeRoot : radius ≤ Real.sqrt radius :=
      (sq_le_sq₀ radiusPositive.le (Real.sqrt_nonneg radius)).mp (by rw [squareRoot]; nlinarith only [inside.2,radiusPositive])
    have cellBound (mode : ℤ × ℤ) : ‖curve radius mode‖ ≤ lower⁻¹*‖row mode radius‖ := by
      have weighted : (Real.sqrt radius : ℂ) • curve radius mode = row mode radius := by
        rw [actual mode,smul_smul,smul_smul]
        convert originalRowCoefficient_weighted parameters power lower row radius radiusPositive mode using 1
        congr 1
        simp only [originalRowWeight,Complex.ofReal_mul,Complex.ofReal_pow]
        ring
      have normWeighted := congrArg norm weighted
      rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg radius)] at normWeighted
      have below := (mul_le_mul_of_nonneg_right (inside.1.trans radiusLeRoot) (norm_nonneg (curve radius mode))).trans_eq normWeighted
      rw [mul_comm lower⁻¹,← div_eq_mul_inv]
      exact (le_div_iff₀ positive).mpr (by simpa only [mul_comm] using below)
    have square : ‖curve radius‖^2 = ∑' mode, ‖curve radius mode‖^2 := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using
        (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (curve radius))
    rw [square,ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (lp_summable_sq (curve radius))]
    unfold physicalBulkSquare
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro mode
    rw [← ENNReal.ofReal_mul (sq_nonneg _),← mul_pow]
    exact ENNReal.ofReal_le_ofReal ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr positive.le) (norm_nonneg _))).mpr (cellBound mode))
  calc
    _ ≤ ∫⁻ radius in Icc lower 1, ENNReal.ofReal ((lower⁻¹)^2)*physicalBulkSquare dimension lower row radius :=
      lintegral_mono_ae point
    _ = ENNReal.ofReal ((lower⁻¹)^2)*(∫⁻ radius in Icc lower 1, physicalBulkSquare dimension lower row radius) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by rw [physicalBulkSquare_integral,← ENNReal.ofReal_mul (sq_nonneg _),mul_pow]

end Grad.OriginalCartesianTameEstimate
