import AEE4CompleteLowReferenceBulkAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators ENNReal
namespace Grad.AnnularLowCompletion
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra
open Grad.AnnularVariational Grad.AnnularSourceGraph
open Grad.GaugeCoefficients.Physical.WeightedTrace

def lowStoredCoordinate (lower length : ℝ) (positive : 0 < lower) (entry : Fin 2) :
    lowEnergyGraph lower length positive →L[ℂ] LowEnergyBulk lower :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => LowEnergyBulk lower) entry).comp
    (lowEnergyGraph lower length positive).subtypeL

theorem lowStoredCoordinate_bound (lower length : ℝ) (positive : 0 < lower) (entry : Fin 2)
    (field : lowEnergyGraph lower length positive) :
    ‖lowStoredCoordinate lower length positive entry field‖ ≤ ‖field‖ := by
  have square := lowEnergyGraph_norm_sq lower length positive field
  fin_cases entry
  · change ‖field.val 0‖ ≤ ‖field‖
    nlinarith [norm_nonneg field, sq_nonneg ‖field.val 1‖]
  · change ‖field.val 1‖ ≤ ‖field‖
    nlinarith [norm_nonneg field, sq_nonneg ‖field.val 0‖]

/-- rho^1/2 mu^-1(w'-Gref w) on the actual closed low graph. -/
def lowReferenceResidual (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) :
    lowEnergyGraph lower length positive →L[ℂ] LowEnergyBulk lower :=
  lowStoredCoordinate lower length positive 1 -
    (lowReferenceBulk parameters length lower lengthPositive positive).comp
      (lowStoredCoordinate lower length positive 0)

theorem lowReferenceResidual_bound (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower)
    (field : lowEnergyGraph lower length positive) :
    ‖lowReferenceResidual parameters length lower lengthPositive positive field‖ ≤
      (1 + 2 * lowReferenceCoefficientConstant parameters length) * ‖field‖ := by
  have first := lowStoredCoordinate_bound lower length positive 1 field
  change ‖field.val 1‖ ≤ ‖field‖ at first
  have second := lowReferenceBulk_bound parameters length lower lengthPositive positive (field.val 0)
  have stored := lowStoredCoordinate_bound lower length positive 0 field
  change ‖field.val 0‖ ≤ ‖field‖ at stored
  have coefficient := (lowReferenceCoefficientConstant_pos parameters length lengthPositive).le
  have comparison := mul_le_mul_of_nonneg_left stored (show 0 ≤ 2 * lowReferenceCoefficientConstant parameters length by positivity)
  change ‖field.val 1 - lowReferenceBulk parameters length lower lengthPositive positive (field.val 0)‖ ≤ _
  exact (norm_sub_le _ _).trans (by nlinarith only [first, second, comparison])

/-- Actual reference Cauchy data map in the original complete BE18 space:
normalized residual and the graph's genuine incoming trace. -/
def lowReferenceDataOperator (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1) :
    lowEnergyGraph lower length positive →L[ℂ] LowEnergyData lower :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (LowEnergyBulk lower) LowEnergyBoundary).symm.toContinuousLinearMap.comp
    ((lowReferenceResidual parameters length lower lengthPositive positive).prod
      (lowIncomingTrace lower length positive bounded))

theorem lowReferenceDataOperator_residual (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) :
    (lowReferenceDataOperator parameters length lower lengthPositive positive bounded field).ofLp.1 =
      lowReferenceResidual parameters length lower lengthPositive positive field := rfl

theorem lowReferenceDataOperator_incoming (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) :
    (lowReferenceDataOperator parameters length lower lengthPositive positive bounded field).ofLp.2 =
      lowIncomingTrace lower length positive bounded field := rfl

end Grad.AnnularLowCompletion
