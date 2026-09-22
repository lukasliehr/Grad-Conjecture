import AIU12UniformCoupledFullDataBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularCurrentSource
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularCrossMaps Grad.AnnularUniformBoundary
open Grad.AnnularCoupledInverse Grad.AnnularKnownLow Grad.AnnularLowEnergy Grad.AnnularCurrentLow
open Grad.GaugeCoefficients.Physical.Allocation

/-- The sourced coupled equation on arbitrary elements of the original
complete high and low graphs. Sources and off-diagonal terms occur once. -/
def CoupledSourceEquation (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (data : IndependentCoupledData parameters lower positive (lowerHalf.trans (by norm_num)))
    (candidate : CoupledSpace lower L positive lengthPositive) : Prop :=
  HighSourceEquation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (addCrossData parameters lower
      (ActualHighKnownCarrier.toGraphKnownData parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data.ofLp.1)
      (lowToHighCross parameters lower L compact lengthPositive positive lowerHalf state candidate.ofLp.2)) candidate.ofLp.1 ∧
  lowCurrentDataOperator parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state candidate.ofLp.2 =
    knownLowDataMap parameters L compact lower positive (lowerHalf.trans (by norm_num)) state data.ofLp.2 +
      highToLowCross parameters lower L compact lengthPositive positive (lowerHalf.trans (by norm_num)) state candidate.ofLp.1

/-- One physical B8 neighborhood and one data constant, both fixed before
choosing the collar or background. The exact original weak rows and physical
boundary reconstruction of this same solution are proved in AIU6--9. -/
theorem completeSourcedCoupled_oneBall (parameters : PhaseParameters) (L compact : ℝ)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
        (state : RetainedInverseState parameters L compact)
        (_small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ δ)
        (data : IndependentCoupledData parameters lower positive (lowerHalf.trans (by norm_num))),
        (∃! solution : CoupledSpace lower L positive lengthPositive,
          CoupledSourceEquation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data solution) ∧
        (∀ solution : CoupledSpace lower L positive lengthPositive,
          CoupledSourceEquation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data solution →
          ‖solution‖ ≤ C * ‖data‖) := by
  refine ⟨coupledPrimitiveRadius parameters L compact, independentCoupledDataConstant parameters L compact,
    coupledPrimitiveRadius_positive parameters L compact lengthPositive, independentCoupledDataConstant_nonnegative parameters L compact, ?_⟩
  intro lower positive lowerHalf state small data
  let high := ActualHighKnownCarrier.toGraphKnownData parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data.ofLp.1
  let solution := independentCoupledResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  constructor
  · refine ⟨solution, ?_, ?_⟩
    · exact ⟨coupledKnownResponse_high parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small high data.ofLp.2,
        coupledKnownResponse_low parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small high data.ofLp.2⟩
    · intro candidate equation
      exact coupledKnownResponse_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
        high data.ofLp.2 candidate equation.1 equation.2
  · intro candidate equation
    have same := coupledKnownResponse_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      high data.ofLp.2 candidate equation.1 equation.2
    rw [same]
    exact independentCoupledResponse_uniform parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data

end Grad.AnnularFullSource
