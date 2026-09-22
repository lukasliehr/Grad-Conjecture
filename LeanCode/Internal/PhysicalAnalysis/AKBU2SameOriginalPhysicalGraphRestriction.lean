import AKBU1SamePhysicalRetainedRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
namespace Grad.OriginalPhysicalKernelUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.AnnularRestriction
open Grad.AnnularLowEnergy Grad.AnnularCoupledInverse Grad.AnnularHighTilt Grad.AnnularTiltedReference
open Grad.AnnularWeakExhaustion
open Grad.AnnularFullGraph Grad.AnnularOriginalCoreRealization Grad.OriginalKernelGraphRestriction
open Grad.SourceCollarCoefficients Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

variable (parameters : PhaseParameters) (length compact lower upper : ℝ)
    (positiveLower : 0<lower) (positiveUpper : 0<upper)
    (domainLower : lower≤min (1/2) length) (domainUpper : upper≤min (1/2) length)
    (lengthPositive : 0<length) (included : lower≤upper)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤originalCoefficientLowRadius parameters length)
    (total vector : ACore parameters 3) (scalar : ACore parameters 1)

/-- The original physical U,S give one compatible retained family on all
collars. This proves the SAME graph restriction, with no weighted-membership
or compatibility premise on the original physical field. -/
theorem originalPhysicalWeightedGraph_restrict :
    coupledEndpointRestriction lower upper length positiveLower positiveUpper
      ((domainUpper.trans (min_le_left _ _)).trans_lt (by norm_num)) lengthPositive included
      (originalWeightedRetainedObservation parameters lower length positiveLower
        ((domainLower.trans (min_le_left _ _)).trans (by norm_num)) lengthPositive
        (originalPhysicalKernelGraphPoint parameters length compact lower positiveLower domainLower lengthPositive state small total vector scalar))=
    originalWeightedRetainedObservation parameters upper length positiveUpper
      ((domainUpper.trans (min_le_left _ _)).trans (by norm_num)) lengthPositive
      (originalPhysicalKernelGraphPoint parameters length compact upper positiveUpper domainUpper lengthPositive state small total vector scalar) := by
  let bounded : upper<1 := (domainUpper.trans (min_le_left _ _)).trans_lt (by norm_num)
  apply sameCoupledCoefficients_faithful parameters upper length positiveUpper bounded lengthPositive
  · intro radius mode
    rw [originalXiCoefficient_restrict]
    exact (originalPhysicalKernelGraphPoint_Xi parameters length compact lower positiveLower domainLower lengthPositive state small total vector scalar
      ⟨radius.val,included.trans radius.property.1,radius.property.2⟩ mode).trans
      (originalPhysicalKernelGraphPoint_Xi parameters length compact upper positiveUpper domainUpper lengthPositive state small total vector scalar radius mode).symm
  · intro radius mode
    rw [originalXCoefficient_restrict]
    exact (originalPhysicalKernelGraphPoint_X parameters length compact lower positiveLower domainLower lengthPositive state small total vector scalar
      ⟨radius.val,included.trans radius.property.1,radius.property.2⟩ mode).trans
      (originalPhysicalKernelGraphPoint_X parameters length compact upper positiveUpper domainUpper lengthPositive state small total vector scalar radius mode).symm

end Grad.OriginalPhysicalKernelUniqueness
