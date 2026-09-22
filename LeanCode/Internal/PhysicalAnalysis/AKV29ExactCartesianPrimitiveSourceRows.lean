import AKV28ActualFullG3RadialCurves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarRestriction Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.SourceCollarBulk
open Grad.SourceCollarAngular Grad.AnnularSourceGraph Grad.AnnularCurrentSource
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation Grad.BoundaryKernelAction

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (source : SmoothQuotient parameters)

theorem actualOriginalF0Bulk_exact :
    unweightedSourceF0Bulk parameters lower (actualOriginalF0Graph parameters lower positive bounded 0 source) =
      tangentialRowContraction lower positive 0
        (cartesianWeightedRadialRow parameters lower positive bounded (cartesianSourceVector source) 0 0) := by
  apply lp.ext
  funext mode
  change (sourceGradeRatio 0 0 1 0 mode : ℝ) •
    annularSourceCoordinate parameters 1 lower 1 0 0
      (actualOriginalF0Graph parameters lower positive bounded 0 source) mode = _
  rw [actualOriginalF0Graph_value]
  change (sourceGradeRatio 0 0 1 0 mode : ℝ) • (annularS11Ratio mode • _) = _
  rw [(restrictedCore_frame_inserted parameters (cartesianSourceVector source) lower positive bounded.le 1 0 mode).2,
    cartesianRestrictionRow_exact parameters lower positive bounded]
  let value : RadialL2 1 lower := tangentialRowContraction lower positive 0
    (cartesianWeightedRadialRow parameters lower positive bounded (cartesianSourceVector source) 0 0) mode
  change (sourceGradeRatio 0 0 1 0 mode : ℝ) • (annularS11Ratio mode • ((annularFrequency mode.1 mode.2 : ℂ)^1 • value)) = value
  rw [← radialL2_real_smul 1 lower (sourceGradeRatio 0 0 1 0 mode),smul_smul,smul_smul]
  have angular : (1+|(mode.1 : ℝ)| : ℝ) ≠ 0 := by positivity
  have scalar : (sourceGradeRatio 0 0 1 0 mode : ℂ) *
      (annularS11Ratio mode * (annularFrequency mode.1 mode.2 : ℂ)^1) = 1 := by
    rw [annularS11Ratio_weight 0 mode]
    simp only [pow_zero,mul_one]
    unfold sourceGradeRatio splitTangentialWeight
    push_cast
    field_simp
    exact div_self (by exact_mod_cast angular)
  rw [mul_assoc,scalar,one_smul]

theorem actualOriginalF1Bulk_exact :
    actualOriginalF1Row parameters lower positive bounded.le 0 source =
      radialRowContraction lower positive 0
        (cartesianWeightedRadialRow parameters lower positive bounded (cartesianSourceVector source) 0 0) := by
  rw [actualOriginalF1Row_value]
  apply lp.ext
  funext mode
  change annularWeightLoweringRatio mode • _ = _
  rw [(restrictedCore_frame_inserted parameters (cartesianSourceVector source) lower positive bounded.le 1 0 mode).1,
    cartesianRestrictionRow_exact parameters lower positive bounded]
  change (annularFrequency mode.1 mode.2 : ℂ)⁻¹ • ((annularFrequency mode.1 mode.2 : ℂ)^1 • _) = _
  rw [pow_one,inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (annularFrequency_pos mode.1 mode.2).ne')]

theorem actualOriginalF2Bulk_exact (length : ℝ) :
    unweightedSourceF2Bulk parameters lower (actualOriginalF2Graph parameters length lower positive bounded 0 source) =
      (length : ℂ)⁻¹ • cartesianWeightedRadialRow parameters lower positive bounded (source 3) 0 0 := by
  rw [unweightedSourceF2Bulk,actualOriginalF2Graph_value,cartesianRestrictionRow_exact parameters lower positive bounded]

/-- The second known slot is exactly R applied to the SAME F0 source. -/
theorem unweightedSourceRF0Bulk_same_angular
    (graph : AnnularSourceH1 parameters 1 lower 1 0) (mode : ℤ × ℤ) :
    unweightedSourceRF0Bulk parameters lower graph mode =
      (Complex.I*(mode.1 : ℂ)) • unweightedSourceF0Bulk parameters lower graph mode := by
  let value : RadialL2 1 lower := annularSourceCoordinate parameters 1 lower 1 0 0 graph mode
  change sourceAngularRatio mode • value = (Complex.I*(mode.1 : ℂ)) • ((sourceGradeRatio 0 0 1 0 mode : ℝ) • value)
  rw [← radialL2_real_smul 1 lower (sourceGradeRatio 0 0 1 0 mode),smul_smul]
  congr 1
  unfold sourceAngularRatio sourceGradeRatio splitTangentialWeight
  push_cast
  ring

end Grad.AnnularGeneralSourceRegularity
