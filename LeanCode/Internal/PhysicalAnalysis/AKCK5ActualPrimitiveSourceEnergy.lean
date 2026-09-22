import AKCK4ActualCartesianRestrictionEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.SourceCollarRestriction Grad.SourceCollarFullSource
open Grad.AnnularGeneralSourceRegularity Grad.PhaseAlgebra Grad.AnnularSmoothCore
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation

/-- A bounded action preserves the exact source energy payment. -/
theorem boundedAction_squareEnergy {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (lower : ℝ) (action : E →L[ℂ] F)
    (curve : ℝ → E) (payment : ℝ)
    (energy : (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖curve radius‖^2)) ≤ ENNReal.ofReal (payment^2)) :
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖action (curve radius)‖^2)) ≤
      ENNReal.ofReal ((‖action‖*payment)^2) := by
  calc
    _ ≤ ∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖action‖^2)*ENNReal.ofReal (‖curve radius‖^2) := by
      apply lintegral_mono
      intro radius
      dsimp only
      rw [← ENNReal.ofReal_mul (sq_nonneg _),← mul_pow]
      exact ENNReal.ofReal_le_ofReal ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (action.le_opNorm _))
    _ = ENNReal.ofReal (‖action‖^2)*(∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖curve radius‖^2)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (‖action‖^2)*ENNReal.ofReal (payment^2) := mul_le_mul' (le_refl _) energy
    _ = _ := by rw [← ENNReal.ofReal_mul (sq_nonneg _),mul_pow]

theorem originalRowRadialCurves_transport {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ}
    {row target : DivisionRow dimension lower} (same : row = target)
    (curves : OriginalRowRadialCurves parameters lower target) :
    (Eq.mpr (congrArg (OriginalRowRadialCurves parameters lower) same) curves).curve = curves.curve := by
  cases same
  rfl

/-- All primitive source realizations retain the actual RF0 derivative and
literal length factor. These are the already constructed AKV curves. -/
theorem actualPrimitiveCurve_formulas (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (source : SmoothQuotient parameters)
    (grade : ℕ) (radius : ℝ) :
    actualCartesianPrimitiveCurve parameters length lower positive bounded source 0 grade radius =
      weightedHilbertTangential parameters grade
        (cartesianWeightedRadialCurve parameters lower positive bounded (cartesianSourceVector source) grade 0 radius) ∧
    actualCartesianPrimitiveCurve parameters length lower positive bounded source 1 grade radius =
      hilbertFrequencyOperator parameters 1 (some false) (weightedHilbertTangential parameters (grade+1)
        (cartesianWeightedRadialCurve parameters lower positive bounded (cartesianSourceVector source) (grade+1) 0 radius)) ∧
    actualCartesianPrimitiveCurve parameters length lower positive bounded source 2 grade radius =
      (length : ℂ)⁻¹ • cartesianWeightedRadialCurve parameters lower positive bounded (source 3) grade 0 radius ∧
    actualCartesianPrimitiveCurve parameters length lower positive bounded source 3 grade radius =
      weightedHilbertRadial parameters grade
        (cartesianWeightedRadialCurve parameters lower positive bounded (cartesianSourceVector source) grade 0 radius) := by
  have f0 (power : ℕ) := congrFun (congrFun
    (originalRowRadialCurves_transport
      (actualOriginalF0Bulk_exact parameters lower positive bounded source)
      ((cartesianOriginalRowRadialCurves parameters lower positive bounded (cartesianSourceVector source)).tangential positive)) power) radius
  have f2 := congrFun (congrFun
    (originalRowRadialCurves_transport
      (actualOriginalF2Bulk_exact parameters lower positive bounded source length)
      ((cartesianOriginalRowRadialCurves parameters lower positive bounded (source 3)).smul ((length : ℂ)⁻¹))) grade) radius
  have f1 := congrFun (congrFun
    (originalRowRadialCurves_transport
      (actualOriginalF1Bulk_exact parameters lower positive bounded source)
      ((cartesianOriginalRowRadialCurves parameters lower positive bounded (cartesianSourceVector source)).radial positive)) grade) radius
  exact ⟨f0 grade,congrArg (hilbertFrequencyOperator parameters 1 (some false)) (f0 (grade+1)),f2,f1⟩

/-- The original primitive rows at q+1 require at most q+2 source orders.
The common q+4 payment leaves the full G3 budget untouched. -/
theorem actualPrimitiveCurve_fourEnergy (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ) :
    ∃ constants : Fin 4 → ℝ, (∀ slot, 0 ≤ constants slot) ∧
    ∀ source : SmoothQuotient parameters, ∀ slot : Fin 4,
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal
        (‖actualCartesianPrimitiveCurve parameters length lower positive bounded source slot (grade+1) radius‖^2)) ≤
      ENNReal.ofReal ((constants slot * ‖quotientEta parameters (grade+4) source‖)^2) := by
  let scale : ℕ → ℝ := fun power => lower⁻¹ * Real.sqrt (restrictionRowConstant power 0)
  let tangential := weightedHilbertTangential parameters (grade+1)
  let angular := (hilbertFrequencyOperator parameters 1 (some false)).comp (weightedHilbertTangential parameters (grade+2))
  let axial : CellL2 1 →L[ℂ] CellL2 1 := (length : ℂ)⁻¹ • ContinuousLinearMap.id ℂ (CellL2 1)
  let radial := weightedHilbertRadial parameters (grade+1)
  refine ⟨![‖tangential‖*scale (grade+1),‖angular‖*scale (grade+2),
    ‖axial‖*scale (grade+1),‖radial‖*scale (grade+1)],?_,?_⟩
  · intro slot
    fin_cases slot <;> change 0 ≤ ‖_‖*(lower⁻¹*Real.sqrt _) <;> positivity
  intro source slot
  have planar (power : ℕ) (paid : power+0≤grade+4) :
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal
        (‖cartesianWeightedRadialCurve parameters lower positive bounded (cartesianSourceVector source) power 0 radius‖^2)) ≤
      ENNReal.ofReal ((scale power*‖quotientEta parameters (grade+4) source‖)^2) := by
    apply (actualCartesianCurve_collarEnergy parameters lower positive bounded paid (cartesianSourceVector source)).trans
    apply ENNReal.ofReal_le_ofReal
    apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
    exact mul_le_mul_of_nonneg_left (originalPlanarCore_norm_le parameters (grade+4) source) (by positivity)
  have scalar :
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal
        (‖cartesianWeightedRadialCurve parameters lower positive bounded (source 3) (grade+1) 0 radius‖^2)) ≤
      ENNReal.ofReal ((scale (grade+1)*‖quotientEta parameters (grade+4) source‖)^2) := by
    apply (actualCartesianCurve_collarEnergy parameters lower positive bounded (by omega : grade+1+0≤grade+4) (source 3)).trans
    apply ENNReal.ofReal_le_ofReal
    apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
    exact mul_le_mul_of_nonneg_left (originalScalarCore_norm_le parameters (grade+4) source 3) (by positivity)
  have formulas := actualPrimitiveCurve_formulas parameters length lower positive bounded source (grade+1)
  have first : (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖actualCartesianPrimitiveCurve parameters length lower positive bounded source 0 (grade+1) radius‖^2)) ≤
      ENNReal.ofReal ((‖tangential‖*scale (grade+1)*‖quotientEta parameters (grade+4) source‖)^2) := by
    simp_rw [(formulas _).1]
    simpa only [tangential,mul_assoc] using
      boundedAction_squareEnergy lower tangential _ _ (planar (grade+1) (by omega))
  have second : (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖actualCartesianPrimitiveCurve parameters length lower positive bounded source 1 (grade+1) radius‖^2)) ≤
      ENNReal.ofReal ((‖angular‖*scale (grade+2)*‖quotientEta parameters (grade+4) source‖)^2) := by
    simp_rw [(formulas _).2.1]
    simpa only [mul_assoc,angular,ContinuousLinearMap.comp_apply,Nat.add_assoc] using
      boundedAction_squareEnergy lower angular _ _ (planar (grade+2) (by omega))
  have third : (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖actualCartesianPrimitiveCurve parameters length lower positive bounded source 2 (grade+1) radius‖^2)) ≤
      ENNReal.ofReal ((‖axial‖*scale (grade+1)*‖quotientEta parameters (grade+4) source‖)^2) := by
    simp_rw [(formulas _).2.2.1]
    simpa only [mul_assoc,axial,_root_.smul_apply,ContinuousLinearMap.id_apply] using
      boundedAction_squareEnergy lower axial _ _ scalar
  have fourth : (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖actualCartesianPrimitiveCurve parameters length lower positive bounded source 3 (grade+1) radius‖^2)) ≤
      ENNReal.ofReal ((‖radial‖*scale (grade+1)*‖quotientEta parameters (grade+4) source‖)^2) := by
    simp_rw [(formulas _).2.2.2]
    simpa only [radial,mul_assoc] using
      boundedAction_squareEnergy lower radial _ _ (planar (grade+1) (by omega))
  fin_cases slot
  · exact first
  · exact second
  · exact third
  · exact fourth

end Grad.OriginalCartesianTameEstimate
