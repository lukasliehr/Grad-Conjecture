import AEI24ActualUniformCurrentLowInverse

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

open Grad.SourceBoundaryTrace Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.WeightedTrace Grad.CircularHighRegularity
open Grad.AnnularLowVolterra

/-- The actual generator in unweighted w coordinates. Its bulk argument is
still rho-stored; the common radial storage factor is decoded exactly. -/
def lowCurrentGeneratorValue (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) : CollarL2 (ComplexEuclidean 1) lower :=
  collarScalar 1 lower (lowStorageInverse lower positive)
    (lowCurrentBulk parameters length compact lower lengthPositive positive bounded state (field.val 0) index)

theorem lowCurrentInverse_storedEquation (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters length compact)
    (data : LowEnergyData lower) :
    (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data).val 1 =
      lowCurrentBulk parameters length compact lower lengthPositive positive bounded.le state
        ((lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data).val 0) + data.ofLp.1 := by
  have equation := congrArg (fun result : LowEnergyData lower => result.ofLp.1)
    (lowCurrentDataOperator_inverse parameters length compact lower lengthPositive positive bounded state small data)
  change (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data).val 1 -
    lowCurrentBulk parameters length compact lower lengthPositive positive bounded.le state
      ((lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data).val 0) = data.ofLp.1 at equation
  exact (sub_eq_iff_eq_add.mp equation).trans (add_comm _ _)

/-- The derivative here is the original weak derivative of the independent
ADY graph, not a new slope assigned by the inverse. -/
theorem lowCurrentInverse_normalizedEquation (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters length compact)
    (data : LowEnergyData lower) (index : LowAnnularIndex) :
    collarScalar 1 lower (lowMuInverseCurve lower length positive index.2.val.2)
      (lowEnergyDerivative lower length positive index
        (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data).val) =
      lowCurrentGeneratorValue parameters length compact lower lengthPositive positive bounded.le state
        (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data) index +
      lowDataResidual lower positive data index := by
  rw [lowEnergy_normalized_derivative, lowCurrentInverse_storedEquation parameters length compact lower lengthPositive positive bounded state small data]
  change collarScalar 1 lower (lowStorageInverse lower positive) (_ + _) = _
  exact map_add _ _ _

theorem lowCurrentInverse_row_ae (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters length compact)
    (data : LowEnergyData lower) (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowEnergyDerivative lower length positive index
        (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data).val radius =
      lowMu length radius index.2.val.2 •
        (lowCurrentGeneratorValue parameters length compact lower lengthPositive positive bounded.le state
          (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data) index radius +
        lowDataResidual lower positive data index radius) := by
  let solution := lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data
  let generator := lowCurrentGeneratorValue parameters length compact lower lengthPositive positive bounded.le state solution index
  have normalized := lowCurrentInverse_normalizedEquation parameters length compact lower lengthPositive positive bounded state small data index
  filter_upwards [collarScalar_ae 1 lower (lowMuInverseCurve lower length positive index.2.val.2)
      (lowEnergyDerivative lower length positive index solution.val),
    Lp.coeFn_add generator (lowDataResidual lower positive data index), ae_restrict_mem measurableSet_Icc]
    with radius derivative additive inside
  have equation := congrArg (fun value : CollarL2 (ComplexEuclidean 1) lower => value radius) normalized
  change collarScalar 1 lower (lowMuInverseCurve lower length positive index.2.val.2)
    (lowEnergyDerivative lower length positive index solution.val) radius = (generator + lowDataResidual lower positive data index) radius at equation
  rw [derivative, additive] at equation
  change (lowMu length (max lower radius) index.2.val.2)⁻¹ • lowEnergyDerivative lower length positive index solution.val radius = _ at equation
  rw [max_eq_right inside.1] at equation
  change (lowMu length radius index.2.val.2)⁻¹ • lowEnergyDerivative lower length positive index solution.val radius =
    generator radius + lowDataResidual lower positive data index radius at equation
  rw [← equation, smul_smul, mul_inv_cancel₀ (lowMu_pos length radius index.2.val.2 (positive.trans_le inside.1)).ne', one_smul]

end Grad.AnnularCurrentLow
