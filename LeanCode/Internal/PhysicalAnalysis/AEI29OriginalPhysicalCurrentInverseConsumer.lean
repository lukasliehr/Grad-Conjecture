import AEI28LiteralPhysicalCurrentLowRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.ActualBoundaryPrimitives Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Ledger

open Grad.AnnularLowVolterra Grad.SourceCollarCoefficients

/-- One original physical B8 neighborhood, chosen before the annulus and
input, supports the actual current inverse on every original low Y. -/
theorem originalLowCurrentInverse_uniform (parameters : PhaseParameters) (length compact : ℝ)
    (lengthPositive : 0 < length) :
    0 < lowCurrentNeighborhood parameters length compact ∧
    ∀ (state : RetainedInverseState parameters length compact),
      physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters length compact →
      ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1),
        ‖lowCurrentInverse parameters length compact lower lengthPositive positive bounded state‖ ≤
          2 * Real.sqrt (lowReferenceGraphConstant parameters length) :=
  ⟨lowCurrentNeighborhood_pos parameters length compact lengthPositive,
    fun state small lower positive bounded => lowCurrentInverse_bound parameters length compact lower lengthPositive positive bounded state small⟩

/-- Exact immediate current consumer on the original complete weighted graph:
actual inverse laws, uniform Y bound, genuine incoming endpoint, original
physical coordinates, the weak current equation and all three literal
pre-Q physical coefficient sums for the SAME solution. -/
theorem originalLowCurrentInverse_consumer (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters length compact)
    (data : LowEnergyData lower) :
    let solution := lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data
    lowCurrentDataOperator parameters length compact lower lengthPositive positive bounded state solution = data ∧
    ‖solution‖ ≤ (2 * Real.sqrt (lowReferenceGraphConstant parameters length)) * ‖data‖ ∧
    (∀ field : lowEnergyGraph lower length positive,
      lowCurrentDataOperator parameters length compact lower lengthPositive positive bounded state field = data → field = solution) ∧
    (∀ index : LowAnnularIndex, lowEnergyEndpoint lower length positive bounded 0 solution index = lowDataIncoming lower length data index) ∧
    (∀ index : LowAnnularIndex, ∀ radius : Icc lower (1 : ℝ),
      lowPhysicalFactor parameters length radius.val index • lowPhysicalSection parameters lower length positive bounded solution index radius =
        lowEnergySection lower length positive bounded solution index radius) ∧
    (∀ index : LowAnnularIndex, ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowEnergyDerivative lower length positive index solution.val radius = lowMu length radius index.2.val.2 •
        (lowCurrentGeneratorValue parameters length compact lower lengthPositive positive bounded.le state solution index radius +
          lowDataResidual lower positive data index radius)) ∧
    (∀ row : Fin 3, ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (lowPhysicalRowKernel parameters length compact state row (collarRadius lower positive bounded.le radius)).entry
        shift (twoFrequencyTranslation shift mode)
        (lowOriginalSevenCoefficient parameters lower length positive bounded solution radius (twoFrequencyTranslation shift mode)))
        (lowOriginalCurrentRow parameters length compact lower lengthPositive positive bounded state solution row radius mode)) := by
  dsimp only
  refine ⟨lowCurrentDataOperator_inverse parameters length compact lower lengthPositive positive bounded state small data, ?_, ?_,
    lowCurrentInverse_endpoint parameters length compact lower lengthPositive positive bounded state small data,
    lowPhysicalSection_encode parameters lower length positive bounded _,
    lowCurrentInverse_row_ae parameters length compact lower lengthPositive positive bounded state small data,
    fun row => lowOriginalCurrentRow_hasSum parameters length compact lower lengthPositive positive bounded state _ row⟩
  · exact (ContinuousLinearMap.le_opNorm _ data).trans (mul_le_mul_of_nonneg_right
      (lowCurrentInverse_bound parameters length compact lower lengthPositive positive bounded state small) (norm_nonneg data))
  · intro field same
    rw [← same, lowCurrentInverse_dataOperator parameters length compact lower lengthPositive positive bounded state small]

end Grad.AnnularCurrentLow
