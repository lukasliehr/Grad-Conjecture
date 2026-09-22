import AKDK6OriginalEulerSourceActions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ENNReal
namespace Grad.OriginalTerminalAllocation
open Grad.OriginalCartesianTameEstimate Grad.CartesianState Grad.AnnularGeneralSourceRegularity
open Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace Grad.AnnularSmoothCore
open Grad.FlatSourceProjection
open Grad.QuotientProjection Grad.ExhaustionSourceAllocation Grad.NonlinearProduct

/-- Actual F0, RF0, F2 and F1 Euler terminals, retaining the original source,
its full-cell phase and the same fixed collar. Constants precede the source. -/
theorem actualPrimitiveCurve_eulerFourEnergy (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0<lower) (bounded : lower<1) (power rank : ℕ) :
    ∃ constants : Fin 4 → ℝ, (∀ slot, 0≤constants slot) ∧
    ∀ source : SmoothQuotient parameters, ∀ slot : Fin 4,
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal
        (‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank
          (actualCartesianPrimitiveCurve parameters length lower positive bounded source slot power) radius‖^2)) ≤
        ENNReal.ofReal ((constants slot*‖quotientEta parameters (power+rank+4) source‖)^2) := by
  let scale := fun p => originalEulerCurveConstant lower p rank
  let tangential := weightedHilbertTangential parameters power
  let angular := (hilbertFrequencyOperator parameters 1 (some false)).comp (weightedHilbertTangential parameters (power+1))
  let axial : CellL2 1 →L[ℂ] CellL2 1 := (length : ℂ)⁻¹ • ContinuousLinearMap.id ℂ (CellL2 1)
  let radial := weightedHilbertRadial parameters power
  have scale0 (p : ℕ) : 0≤scale p := originalEulerCurveConstant_nonnegative lower positive p rank
  refine ⟨![‖tangential‖*scale power,‖angular‖*scale (power+1),‖axial‖*scale power,‖radial‖*scale power],?_,?_⟩
  · intro slot
    fin_cases slot <;> exact mul_nonneg (norm_nonneg _) (scale0 _)
  intro source slot
  have planar (p : ℕ) (paid : p+rank≤power+rank+4) (action : CellL2 2 →L[ℂ] CellL2 1) :
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal
        (‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank
          (fun point => action (cartesianWeightedRadialCurve parameters lower positive bounded (cartesianSourceVector source) p 0 point)) radius‖^2)) ≤
        ENNReal.ofReal ((‖action‖*scale p*‖quotientEta parameters (power+rank+4) source‖)^2) := by
    apply (actualCartesianAction_eulerEnergy parameters lower positive bounded paid (cartesianSourceVector source) action).trans
    apply ENNReal.ofReal_le_ofReal
    apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (mul_nonneg (scale0 _) (originalGradeNorm_nonnegative _ _)))
      (mul_nonneg (mul_nonneg (norm_nonneg _) (scale0 _)) (norm_nonneg _))).mpr
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (originalPlanarCore_norm_le parameters (power+rank+4) source)
      (mul_nonneg (norm_nonneg _) (scale0 _))
  have scalar :
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal
        (‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank
          (fun point => axial (cartesianWeightedRadialCurve parameters lower positive bounded (source 3) power 0 point)) radius‖^2)) ≤
        ENNReal.ofReal ((‖axial‖*scale power*‖quotientEta parameters (power+rank+4) source‖)^2) := by
    apply (actualCartesianAction_eulerEnergy parameters lower positive bounded (by omega : power+rank≤power+rank+4) (source 3) axial).trans
    apply ENNReal.ofReal_le_ofReal
    apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (mul_nonneg (scale0 _) (originalGradeNorm_nonnegative _ _)))
      (mul_nonneg (mul_nonneg (norm_nonneg _) (scale0 _)) (norm_nonneg _))).mpr
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (originalScalarCore_norm_le parameters (power+rank+4) source 3)
      (mul_nonneg (norm_nonneg _) (scale0 _))
  have firstSame : actualCartesianPrimitiveCurve parameters length lower positive bounded source 0 power =
      fun radius => tangential (cartesianWeightedRadialCurve parameters lower positive bounded (cartesianSourceVector source) power 0 radius) :=
    funext (fun radius => (actualPrimitiveCurve_formulas parameters length lower positive bounded source power radius).1)
  have secondSame : actualCartesianPrimitiveCurve parameters length lower positive bounded source 1 power =
      fun radius => angular (cartesianWeightedRadialCurve parameters lower positive bounded (cartesianSourceVector source) (power+1) 0 radius) :=
    funext (fun radius => (actualPrimitiveCurve_formulas parameters length lower positive bounded source power radius).2.1)
  have thirdSame : actualCartesianPrimitiveCurve parameters length lower positive bounded source 2 power =
      fun radius => axial (cartesianWeightedRadialCurve parameters lower positive bounded (source 3) power 0 radius) :=
    funext (fun radius => (actualPrimitiveCurve_formulas parameters length lower positive bounded source power radius).2.2.1)
  have fourthSame : actualCartesianPrimitiveCurve parameters length lower positive bounded source 3 power =
      fun radius => radial (cartesianWeightedRadialCurve parameters lower positive bounded (cartesianSourceVector source) power 0 radius) :=
    funext (fun radius => (actualPrimitiveCurve_formulas parameters length lower positive bounded source power radius).2.2.2)
  let energyOf (curve : ℝ → CellL2 1) : ℝ≥0∞ :=
    ∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank curve radius‖^2)
  have first := (congrArg energyOf firstSame).le.trans (planar power (by omega) tangential)
  have second := (congrArg energyOf secondSame).le.trans (planar (power+1) (by omega) angular)
  have third := (congrArg energyOf thirdSame).le.trans scalar
  have fourth := (congrArg energyOf fourthSame).le.trans (planar power (by omega) radial)
  fin_cases slot
  · exact first
  · exact second
  · exact third
  · exact fourth

end Grad.OriginalTerminalAllocation
