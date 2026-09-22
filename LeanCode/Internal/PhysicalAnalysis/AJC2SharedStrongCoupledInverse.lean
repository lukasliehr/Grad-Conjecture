import AJC1SameSharedCoupledData
import AIU13CompleteSourcedCoupledConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularStrongSolution
open Grad.ClosedJets Grad.CartesianState Grad.AnnularCurrentSource
open Grad.AnnularReconstruction
open Grad.AnnularFullSource Grad.AnnularStrongData Grad.AnnularKnownLow Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)

/-- The original full sourced equation on the actual coupled graph, with
one prescribed strong datum supplying both physical diagonal source maps. -/
def StrongCoupledEquation
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (solution : CoupledSpace lower L positive lengthPositive) : Prop :=
  CoupledSourceEquation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (strongToIndependent parameters lower positive (lowerHalf.trans (by norm_num)) data) solution

variable (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
    coupledPrimitiveRadius parameters L compact)

/-- This is the SAME constructed coupled inverse, applied to both projections
of the shared source, not a new inverse or a chosen candidate. -/
def sharedStrongResponse
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    CoupledSpace lower L positive lengthPositive :=
  independentCoupledResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (strongToIndependent parameters lower positive (lowerHalf.trans (by norm_num)) data)

theorem sharedStrongResponse_bound
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    let solution : CoupledSpace lower L positive lengthPositive :=
      sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
    ‖solution‖ ≤ 2 * independentCoupledDataConstant parameters L compact * ‖data‖ := by
  have initial := independentCoupledResponse_uniform parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (strongToIndependent parameters lower positive (lowerHalf.trans (by norm_num)) data)
  apply initial.trans
  calc
    independentCoupledDataConstant parameters L compact *
        ‖strongToIndependent parameters lower positive (lowerHalf.trans (by norm_num)) data‖ ≤
      independentCoupledDataConstant parameters L compact * (2 * ‖data‖) :=
      mul_le_mul_of_nonneg_left
        (strongToIndependent_bound parameters lower positive (lowerHalf.trans (by norm_num)) data)
        (independentCoupledDataConstant_nonnegative parameters L compact)
    _ = _ := by ring

theorem sharedStrongResponse_equation
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    StrongCoupledEquation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data
      (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) := by
  let high := ActualHighKnownCarrier.toGraphKnownData parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
    (strongToHigh parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data)
  exact ⟨coupledKnownResponse_high parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small high
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data),
    coupledKnownResponse_low parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small high
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data)⟩

theorem sharedStrongResponse_unique
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (candidate : CoupledSpace lower L positive lengthPositive)
    (equation : StrongCoupledEquation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data candidate) :
    candidate = sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data :=
  coupledKnownResponse_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (ActualHighKnownCarrier.toGraphKnownData parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
      (strongToHigh parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data))
    (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data) candidate equation.1 equation.2

/-- One positive original B8 ball and one single-data norm coefficient,
chosen before the collar and background. No cap or frequency carrier enters. -/
theorem sharedStrongCoupled_oneBall (parameters : PhaseParameters) (L compact : ℝ)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
        (state : RetainedInverseState parameters L compact)
        (_small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ δ)
        (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0),
        (∃! solution : CoupledSpace lower L positive lengthPositive,
          StrongCoupledEquation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data solution) ∧
        (∀ solution : CoupledSpace lower L positive lengthPositive,
          StrongCoupledEquation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data solution →
          ‖solution‖ ≤ C * ‖data‖) := by
  refine ⟨coupledPrimitiveRadius parameters L compact, 2 * independentCoupledDataConstant parameters L compact,
    coupledPrimitiveRadius_positive parameters L compact lengthPositive,
    mul_nonneg (by norm_num) (independentCoupledDataConstant_nonnegative parameters L compact), ?_⟩
  intro lower positive lowerHalf state small data
  constructor
  · exact ⟨sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data,
      sharedStrongResponse_equation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data,
      fun candidate equation => sharedStrongResponse_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data candidate equation⟩
  · intro candidate equation
    rw [sharedStrongResponse_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data candidate equation]
    exact sharedStrongResponse_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data

end Grad.AnnularStrongSolution
