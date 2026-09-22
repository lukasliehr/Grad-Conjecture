import AIW8UniformToAJCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOriginalLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.PhaseAlgebra Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem originalLowToAJ_curves_bound (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1)
    (index : LowAnnularIndex) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |originalLowToAJValueCurve parameters lower length positive index radius| ≤ originalLowToAJConstant parameters length * lower⁻¹ ∧
    |originalLowToAJCorrectionCurve parameters lower length positive index radius| ≤ originalLowToAJConstant parameters length * lower⁻¹ ∧
    |originalLowToAJSlopeCurve parameters lower length positive index radius| ≤ originalLowToAJConstant parameters length * lower⁻¹ := by
  have factors := originalLowToAJ_factors_bound parameters lower length positive lengthPositive bounded index radius inside
  have storage := originalLow_storage_bounds lower radius positive inside
  have frequency := cellFrequency_pos index.2.val.2
  have muPositive := lowMu_pos length radius index.2.val.2 (positive.trans_le inside.1)
  have boundPositive : 0 ≤ originalLowToAJConstant parameters length * lower⁻¹ :=
    mul_nonneg (zero_le_one.trans (originalLowToAJConstant_dominates parameters length lengthPositive).2.2.2)
      (inv_nonneg.mpr positive.le)
  constructor
  · change |originalLowRatio parameters lower length positive index radius * lowStorageInverse lower positive radius| ≤ _
    rw [abs_mul, abs_of_pos storage.1]
    exact (mul_le_mul factors.1 storage.2.1 storage.1.le boundPositive).trans_eq (mul_one _)
  constructor
  · change |(cellFrequency index.2.val.2)⁻¹ *
      (originalLowRatioSlope parameters lower length positive index radius * lowStorageInverse lower positive radius)| ≤ _
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr frequency), abs_of_pos storage.1]
    have equality : (cellFrequency index.2.val.2)⁻¹ *
        (|originalLowRatioSlope parameters lower length positive index radius| * lowStorageInverse lower positive radius) =
      (|originalLowRatioSlope parameters lower length positive index radius| / cellFrequency index.2.val.2) *
        lowStorageInverse lower positive radius := by ring
    rw [equality]
    exact (mul_le_mul factors.2.1 storage.2.1 storage.1.le boundPositive).trans_eq (mul_one _)
  · change |(cellFrequency index.2.val.2)⁻¹ *
      (originalLowRatio parameters lower length positive index radius *
        lowMuCurve lower length positive index.2.val.2 radius * lowStorageInverse lower positive radius)| ≤ _
    have physical : lowMuCurve lower length positive index.2.val.2 radius = lowMu length radius index.2.val.2 := by
      change lowMu length (max lower radius) index.2.val.2 = _
      rw [max_eq_right inside.1]
    rw [physical, abs_mul, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr frequency),
      abs_of_pos muPositive, abs_of_pos storage.1]
    have equality : (cellFrequency index.2.val.2)⁻¹ *
        (|originalLowRatio parameters lower length positive index radius| *
          lowMu length radius index.2.val.2 * lowStorageInverse lower positive radius) =
      (|originalLowRatio parameters lower length positive index radius| *
          lowMu length radius index.2.val.2 / cellFrequency index.2.val.2) *
        lowStorageInverse lower positive radius := by ring
    rw [equality]
    exact (mul_le_mul factors.2.2 storage.2.1 storage.1.le boundPositive).trans_eq (mul_one _)

/-- Reuses the actual matrix-multiplier realization to bound collarScalar. -/
theorem originalLow_scalar_bound (lower : ℝ) (curve : C(ℝ, ℝ)) (bound : ℝ)
    (bounded : ∀ radius, radius ∈ Icc lower 1 → |curve radius| ≤ bound)
    (field : CollarL2 (ComplexEuclidean 1) lower) : ‖collarScalar 1 lower curve field‖ ≤ bound * ‖field‖ := by
  have same : collarScalar 1 lower curve field = scalarRadialMap lower curve bound bounded field := by
    apply Lp.ext
    filter_upwards [collarScalar_ae 1 lower curve field, scalarRadialMap_ae lower curve bound bounded field]
      with radius first second
    exact first.trans second.symm
  rw [same]
  exact scalarRadialMap_bound lower curve bound bounded field

def originalLowScalarFamily (lower : ℝ) (curves : LowAnnularIndex → C(ℝ, ℝ))
    (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ index radius, radius ∈ Icc lower 1 → |curves index radius| ≤ bound) :
    LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower :=
  complexLpTwoMap (fun index => collarScalar 1 lower (curves index)) bound nonnegative
    (fun index field => originalLow_scalar_bound lower (curves index) bound (bounded index) field)

theorem originalLowScalarFamily_apply (lower : ℝ) (curves : LowAnnularIndex → C(ℝ, ℝ))
    (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ index radius, radius ∈ Icc lower 1 → |curves index radius| ≤ bound)
    (field : LowEnergyBulk lower) (index : LowAnnularIndex) :
    originalLowScalarFamily lower curves bound nonnegative bounded field index =
      collarScalar 1 lower (curves index) (field index) := rfl

theorem originalLowScalarFamily_bound (lower : ℝ) (curves : LowAnnularIndex → C(ℝ, ℝ))
    (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ index radius, radius ∈ Icc lower 1 → |curves index radius| ≤ bound)
    (field : LowEnergyBulk lower) :
    ‖originalLowScalarFamily lower curves bound nonnegative bounded field‖ ≤ bound * ‖field‖ :=
  complexLpTwoMap_bound _ _ _ _ field

end Grad.AnnularOriginalLow
