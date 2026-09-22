import AIQ4DirectGraphPhysicalBoundary

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.AnnularPhysicalSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentGreen Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse
open Grad.AnnularCurrentSource Grad.AnnularCurrentBoundary Grad.AnnularOmegaGraph Grad.AnnularKernelL2
open Grad.AnnularReconstruction Grad.AnnularUniformBoundary Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives
open Grad.ActualBoundaryInverse

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (state : RetainedInverseState parameters L compact)

/-- Direct BCT13 physical boundary equals the complete graph datum exactly when the genuine outer x is the affine row. -/
theorem candidatePhysicalBoundary_iff (data : ActualHighGraphKnownData parameters lower 0 0)
    (candidate : annularEnergySpace lower L positive) (x : HighBoundaryPrimitive parameters 0 0) :
    graphNativePhysicalBoundary state.outerInverseState 0 0 x
      (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 candidate)
      (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 data.graphs) = data.datum ↔
      x = candidatePhysicalOuter parameters L compact lower positive lowerHalf lengthPositive state data candidate := by
  rw [graphNativePhysicalBoundary_inverse_iff]
  rfl

/-- The SAME variationally recovered flux satisfies the literal graph-native physical boundary, even at base grade zero. -/
theorem graphDataPhysicalBoundary_eq_datum
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)
    (data : ActualHighGraphKnownData parameters lower 0 0) :
    graphNativePhysicalBoundary state.outerInverseState 0 0
      (graphDataPhysicalOuter parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
      (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0
        (graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data))
      (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 data.graphs) = data.datum := by
  apply (candidatePhysicalBoundary_iff parameters L compact lower positive lowerHalf lengthPositive state data
    (graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
    (graphDataPhysicalOuter parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)).mpr
  rfl

end Grad.AnnularPhysicalSolution
