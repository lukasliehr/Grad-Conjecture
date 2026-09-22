import AKBA11ExactOriginalRetainedCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.OriginalKernelGraphRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.SourceCollarFullSource
open Grad.AnnularReconstruction Grad.AnnularOriginalSmoothCore Grad.AnnularOriginalCoreRealization
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularFullGraph Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.AnnularCurrentSource Grad.OriginalKernelRetainedDecay

theorem originalTupleObservation_copiedSources_zero {parameters : PhaseParameters} {length compact lower : ℝ}
    {positive : 0<lower} {bounded : lower<1} {lengthPositive : 0<length}
    {state : RetainedInverseState parameters length compact} {tuple : OriginalSmoothTuple parameters lower}
    {point : OriginalFiveBlockAmbient parameters lower length positive}
    (represented : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state tuple point)
    (firstZero : tuple.val 2=0) (secondZero : tuple.val 3=0) : point.ofLp.2.ofLp.1=0 := by
  have zeroRep : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state 0 0 := by
    simpa only [map_zero] using
      originalTupleGraphLinear_represents parameters length compact lower positive bounded lengthPositive state 0
  have first : point.ofLp.2.ofLp.1.ofLp.1=0 := by
    apply unweightedSourceF0Bulk_faithful parameters lower positive bounded.le
    apply originalF1Coefficient_faithful parameters lower positive bounded.le
    filter_upwards [represented.sourceZero,zeroRep.sourceZero] with radius actual zero
    intro mode
    exact ((actual mode).symm.trans (congrArg (fun field => originalPhysicalCoefficient field radius mode) firstZero)).trans (zero mode)
  have second : point.ofLp.2.ofLp.1.ofLp.2=0 := by
    apply unweightedSourceF2Bulk_faithful parameters lower positive bounded.le
    apply originalF1Coefficient_faithful parameters lower positive bounded.le
    filter_upwards [represented.sourceTwo,zeroRep.sourceTwo] with radius actual zero
    intro mode
    exact ((actual mode).symm.trans (congrArg (fun field => originalPhysicalCoefficient field radius mode) secondZero)).trans (zero mode)
  exact (WithLp.equiv 2 _).injective (Prod.ext first second)

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0<lower)
    (domain : lower≤min (1/2) length) (lengthPositive : 0<length)
    (state : RetainedInverseState parameters length compact)
    (coefficientSmall : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤originalCoefficientLowRadius parameters length)
    (total vector : ACore parameters 3) (scalar : ACore parameters 1)

/-- Both copied original H1 source graphs vanish, including their actual
radial derivatives and both traces, for the same physical kernel tuple. -/
theorem originalPhysicalKernelGraphPoint_copiedSources :
    (originalPhysicalKernelGraphPoint parameters length compact lower positive domain lengthPositive state coefficientSmall total vector scalar).ofLp.2.ofLp.1=0 := by
  apply originalTupleObservation_copiedSources_zero
    (originalPhysicalKernelGraphPoint_represents parameters length compact lower positive domain lengthPositive state coefficientSmall total vector scalar)
  · rfl
  · rfl

end Grad.OriginalKernelGraphRestriction
