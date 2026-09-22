import AKCA1NativeEnergyAxisJetExclusion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Grad.OriginalCoreRealization
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace
open Grad.WeightedAxisRemoval
open Grad.AnnularCurrentLow Grad.ActualPuncturedReconstruction Grad.AnnularIncomingIntegrability

theorem lowRhoPhysicalCoefficient_criticalRadius_bound {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (field : DivisionRow dimension lower)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    ‖radius ^ (-(3 / 2 : ℝ)) • lowRhoPhysicalCoefficient parameters lower positive field radius mode‖ ≤
      radius ^ (1 / 4 : ℝ) * ‖field mode radius‖ := by
  have radiusPositive := positive.trans_le inside.1
  rw [norm_smul,Real.norm_of_nonneg (Real.rpow_nonneg radiusPositive.le (-(3 / 2 : ℝ)))]
  have bound := mul_le_mul_of_nonneg_left
    (lowRhoPhysicalCoefficient_norm_bound parameters lower positive field radius inside mode)
    (Real.rpow_nonneg radiusPositive.le (-(3 / 2 : ℝ)))
  have power : radius ^ (-(3 / 2 : ℝ)) * radius ^ (7 / 4 : ℝ) = radius ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add radiusPositive]
    norm_num
  exact bound.trans_eq (by rw [← mul_assoc,power])

theorem lowRhoPhysicalCoefficient_criticalRadius_contraction {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (field : DivisionRow dimension lower)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    ‖radius ^ (-(3 / 2 : ℝ)) • lowRhoPhysicalCoefficient parameters lower positive field radius mode‖ ≤ ‖field mode radius‖ := by
  have bound := lowRhoPhysicalCoefficient_criticalRadius_bound parameters lower positive field radius inside mode
  have power : radius ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one (positive.trans_le inside.1).le inside.2 (by norm_num)
  exact bound.trans ((mul_le_mul_of_nonneg_right power (norm_nonneg _)).trans_eq (one_mul _))

/-- Simultaneous angular/cell square summation for the actual physical
Hilbert curve. The critical r^(-3/2) division is controlled by the original r^(-7/4) stored energy. -/
theorem physicalHilbertCurve_criticalRadius_square {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (field : DivisionRow dimension lower)
    (curve : ℝ → CellL2 dimension)
    (same : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      curve radius mode = lowRhoPhysicalCoefficient parameters lower positive field radius mode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      ENNReal.ofReal (‖radius ^ (-(3 / 2 : ℝ)) • curve radius‖ ^ 2) ≤ physicalBulkSquare dimension lower field radius := by
  filter_upwards [same,ae_restrict_mem measurableSet_Icc] with radius same inside
  have sum : ‖radius ^ (-(3 / 2 : ℝ)) • curve radius‖ ^ 2 = ∑' mode, ‖(radius ^ (-(3 / 2 : ℝ)) • curve radius) mode‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using
      (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (radius ^ (-(3 / 2 : ℝ)) • curve radius))
  rw [sum,ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (lp_summable_sq (radius ^ (-(3 / 2 : ℝ)) • curve radius))]
  apply ENNReal.tsum_le_tsum
  intro mode
  apply ENNReal.ofReal_le_ofReal
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
  change ‖radius ^ (-(3 / 2 : ℝ)) • curve radius mode‖ ≤ ‖field mode radius‖
  rw [same mode]
  exact lowRhoPhysicalCoefficient_criticalRadius_contraction parameters lower positive field radius inside mode

end Grad.OriginalCoreRealization
