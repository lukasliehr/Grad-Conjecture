import AAQ4ActualNormalizedFluxSlope

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFluxTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

section Bound
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularFluxPhase_bound (field : AnnularBulk lower) :
    ‖annularFluxPhase parameters lower length positive lengthPositive widthHalf widthLength field‖ ≤
      annularFluxPotentialConstant lower length * ‖field‖ := annularScalarFamily_bound _ _ _ _ _ field

theorem annularFluxInverseRadius_bound (field : AnnularBulk lower) :
    ‖annularFluxInverseRadius lower positive field‖ ≤ lower⁻¹ * ‖field‖ := annularScalarFamily_bound _ _ _ _ _ field

theorem annularFluxInverseSquare_bound (field : AnnularBulk lower) :
    ‖annularFluxInverseSquare lower positive field‖ ≤ (4 * lower⁻¹ ^ 2) * ‖field‖ :=
  annularScalarFamily_bound _ _ _ _ _ field

theorem annularFluxD_bound (field : AnnularBulk lower) :
    ‖annularFluxD lower field‖ ≤ ‖field‖ := by
  simpa only [annularFluxD, one_mul] using annularSymbolFamily_bound lower
    (fun mode => ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ : ℝ) • annularDSymbol mode)
    1 (by norm_num) annularNormalizedD_bound field

theorem annularFluxCell_bound (field : AnnularBulk lower) :
    ‖annularFluxCell lower length lengthPositive field‖ ≤ length⁻¹ * ‖field‖ :=
  annularSymbolFamily_bound _ _ _ _ _ field

theorem annularFluxSlope_physical_bound (data : AnnularFluxAmbient lower length positive) :
    ‖annularFluxSlope parameters lower length positive lengthPositive widthHalf widthLength data‖ ≤
      (annularFluxPotentialConstant lower length + lower⁻¹) *
        ‖annularFluxQ parameters lower length positive lengthPositive widthHalf widthLength data‖ +
      (annularFluxPotentialConstant lower length + (4 / 3 : ℝ) * lower⁻¹ ^ 2) * ‖data.1‖ +
      ‖data.2.2.1‖ + length⁻¹ * ‖data.2.2.2.1‖ := by
  let q := annularFluxQ parameters lower length positive lengthPositive widthHalf widthLength data
  let phase := annularFluxPhase parameters lower length positive lengthPositive widthHalf widthLength q
  let radial := annularFluxInverseRadius lower positive q
  let potential := annularNormalizedPotentialMap lower length positive data.1
  let square := annularFluxInverseSquare lower positive (annularEnergyValue lower length positive data.1)
  let g := annularFluxD lower data.2.2.1
  let f2 := annularFluxCell lower length lengthPositive data.2.2.2.1
  have phaseBound := annularFluxPhase_bound parameters lower length positive lengthPositive widthHalf widthLength q
  have radialBound := annularFluxInverseRadius_bound lower positive q
  have potentialBound := annularNormalizedPotentialMap_bound lower length positive data.1
  have squareBound := (annularFluxInverseSquare_bound lower positive
    (annularEnergyValue lower length positive data.1)).trans
      (mul_le_mul_of_nonneg_left (annularEnergyValue_bound lower length positive data.1) (by positivity))
  have gBound := annularFluxD_bound lower data.2.2.1
  have f2Bound := annularFluxCell_bound lower length lengthPositive data.2.2.2.1
  change ‖phase + radial + potential - square - g - f2‖ ≤ _
  have total : ‖phase + radial + potential - square - g - f2‖ ≤
      ‖phase‖ + ‖radial‖ + ‖potential‖ + ‖square‖ + ‖g‖ + ‖f2‖ := by
    have first := norm_add_le phase radial
    have second := norm_add_le (phase + radial) potential
    have third := norm_sub_le (phase + radial + potential) square
    have fourth := norm_sub_le (phase + radial + potential - square) g
    have fifth := norm_sub_le (phase + radial + potential - square - g) f2
    linarith
  dsimp only [phase, radial, potential, square, g, f2, q] at total ⊢
  nlinarith

def annularFluxSlopeConstant (lower length : ℝ) : ℝ :=
  5 * annularFluxPotentialConstant lower length + 4 * lower⁻¹ +
    (4 / 3 : ℝ) * lower⁻¹ ^ 2 + 1 + length⁻¹

include positive lengthPositive in
theorem annularFluxSlopeConstant_nonnegative : 0 ≤ annularFluxSlopeConstant lower length := by
  unfold annularFluxSlopeConstant
  have := annularFluxPotentialConstant_nonnegative lower length
  positivity

theorem annularFluxQ_bound (data : AnnularFluxAmbient lower length positive) :
    ‖annularFluxQ parameters lower length positive lengthPositive widthHalf widthLength data‖ ≤ 4 * ‖data‖ := by
  have physical := annularRecoveredQ_bound parameters lower length positive lengthPositive widthHalf widthLength data.1 data.2.1
  have stateBound := norm_fst_le data
  have fBound := (norm_fst_le data.2).trans (norm_snd_le data)
  rw [annularFluxQ_apply]
  linarith

theorem annularFluxSlope_bound (data : AnnularFluxAmbient lower length positive) :
    ‖annularFluxSlope parameters lower length positive lengthPositive widthHalf widthLength data‖ ≤
      annularFluxSlopeConstant lower length * ‖data‖ := by
  have physical := annularFluxSlope_physical_bound parameters lower length positive lengthPositive widthHalf widthLength data
  have qBound := mul_le_mul_of_nonneg_left
    (annularFluxQ_bound parameters lower length positive lengthPositive widthHalf widthLength data)
    (add_nonneg (annularFluxPotentialConstant_nonnegative lower length) (inv_nonneg.mpr positive.le))
  have stateBound := mul_le_mul_of_nonneg_left (norm_fst_le data)
    (add_nonneg (annularFluxPotentialConstant_nonnegative lower length)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3) (sq_nonneg lower⁻¹)))
  have gBound := (norm_fst_le data.2.2).trans ((norm_snd_le data.2).trans (norm_snd_le data))
  have f2Bound := mul_le_mul_of_nonneg_left
    ((norm_fst_le data.2.2.2).trans ((norm_snd_le data.2.2).trans ((norm_snd_le data.2).trans (norm_snd_le data))))
    (inv_nonneg.mpr lengthPositive.le)
  unfold annularFluxSlopeConstant
  nlinarith

end Bound
end Grad.AnnularFluxTrace
