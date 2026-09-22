import AAX3ClosedResidualGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFourSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace

def annularKSymbol (mode : HighAnnularMode) : ℂ := (Complex.I * (mode.val.1 : ℂ))⁻¹

theorem annularKSymbol_bound (mode : HighAnnularMode) : ‖annularKSymbol mode‖ ≤ 1 := by
  have high : (3 : ℝ) ≤ |(mode.val.1 : ℝ)| := by exact_mod_cast mode.property
  have castNorm : ‖(mode.val.1 : ℂ)‖ = |(mode.val.1 : ℝ)| := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  rw [annularKSymbol, norm_inv, norm_mul, Complex.norm_I, one_mul, castNorm]
  simpa only [one_div] using (div_le_one (by linarith : 0 < |(mode.val.1 : ℝ)|)).mpr
    (by linarith : (1 : ℝ) ≤ |(mode.val.1 : ℝ)|)

def annularKMap (lower : ℝ) : AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  annularSymbolFamily lower annularKSymbol 1 (by norm_num) annularKSymbol_bound

def annularTwiceKAngular (lower : ℝ) : AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  (2 : ℂ) • (annularKMap lower).comp (annularAngularDecode lower)

theorem annularTwiceKAngular_apply (lower : ℝ) (field : AnnularBulk lower) (mode : HighAnnularMode) :
    annularTwiceKAngular lower field mode = (2 : ℂ) •
      (Complex.I * (mode.val.1 : ℂ))⁻¹ • annularAngularDecode lower field mode := rfl

private theorem firstResidual_pointwise (lower : ℝ) (h r p f : AnnularBulk lower) (mode : HighAnnularMode) :
    (h + r - annularQFromAngularP lower p - annularTwiceKAngular lower f) mode =
      h mode + r mode + annularDSymbol mode • annularAngularDecode lower p mode -
      (2 : ℂ) • (Complex.I * (mode.val.1 : ℂ))⁻¹ • annularAngularDecode lower f mode := by
  change h mode + r mode - annularQFromAngularP lower p mode - annularTwiceKAngular lower f mode = _
  rw [annularQFromAngularP_apply, annularTwiceKAngular_apply, neg_smul, sub_neg_eq_add]

section Residual
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- The literal first residual F1=xi_r+2xi/r+Dp-2K F0.
Every quantity has the original phase-weighted sqrt(r) normalization. -/
def annularFourFirstResidual : AnnularFourAmbient lower length positive →L[ℂ] AnnularBulk lower :=
  annularFourF parameters lower length positive lengthPositive widthHalf widthLength -
    (annularTwiceKAngular lower).comp (annularFourF0 lower length positive)

theorem annularFourFirstResidual_literal (data : AnnularFourAmbient lower length positive) (mode : HighAnnularMode) :
    annularFourFirstResidual parameters lower length positive lengthPositive widthHalf widthLength data mode =
      annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength
          (annularFourW lower length positive data) mode +
        annularEnergyRadial lower length positive (annularFourW lower length positive data) mode +
        annularDSymbol mode • annularAngularDecode lower (annularFourP lower length positive data) mode -
        (2 : ℂ) • (Complex.I * (mode.val.1 : ℂ))⁻¹ •
          annularAngularDecode lower (annularFourF0 lower length positive data) mode := by
  have bulk : annularFourFirstResidual parameters lower length positive lengthPositive widthHalf widthLength data =
      (annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength
        (annularFourW lower length positive data) +
      annularEnergyRadial lower length positive (annularFourW lower length positive data) -
      annularQFromAngularP lower (annularFourP lower length positive data)) -
      annularTwiceKAngular lower (annularFourF0 lower length positive data) := rfl
  exact (congrArg (fun field : AnnularBulk lower => field mode) bulk).trans
    (firstResidual_pointwise lower
      (annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength
        (annularFourW lower length positive data))
      (annularEnergyRadial lower length positive (annularFourW lower length positive data))
      (annularFourP lower length positive data) (annularFourF0 lower length positive data) mode)

end Residual
end Grad.AnnularFourSource
