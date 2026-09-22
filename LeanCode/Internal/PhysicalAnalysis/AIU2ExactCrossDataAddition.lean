import AIU1FullKnownHighResponse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularCurrentSource
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularCrossMaps Grad.AnnularUniformBoundary
open Grad.AnnularCurrentGreen Grad.AnnularOmegaGraph Grad.AnnularPhysicalSolution Grad.AnnularCurrentBoundary
open Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse

/-- The cross source changes only f,qc,rqv and outer datum. Original source
graphs and incoming trace remain exactly those of the prescribed datum. -/
def addCrossData (parameters : PhaseParameters) (lower : ℝ)
    (data : ActualHighGraphKnownData parameters lower 0 0) (cross : CrossHighData parameters lower) :
    ActualHighGraphKnownData parameters lower 0 0 where
  weighted := data.weighted + crossKnownWeighted parameters lower cross
  auxiliary := data.auxiliary + crossKnownAuxiliary parameters lower cross
  graphs := data.graphs
  datum := data.datum + cross.ofLp.2
  innerValue := data.innerValue
  weightedGraph := by
    have first : (data.weighted + crossKnownWeighted parameters lower cross) 0 = data.weighted 0 := by
      change data.weighted 0 + 0 = data.weighted 0
      exact add_zero _
    have second : (data.weighted + crossKnownWeighted parameters lower cross) 1 = data.weighted 1 := by
      change data.weighted 1 + 0 = data.weighted 1
      exact add_zero _
    have third : (data.weighted + crossKnownWeighted parameters lower cross) 2 = data.weighted 2 := by
      change data.weighted 2 + 0 = data.weighted 2
      exact add_zero _
    unfold WeightedGraphCompatibility
    rw [first, second, third]
    exact data.weightedGraph

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)

/-- Literal affine known functional: the physical source graph trace is
counted once and the actual BF16 functional is added once. -/
theorem addCrossData_functional (data : ActualHighGraphKnownData parameters lower 0 0)
    (cross : CrossHighData parameters lower) (test : annularEnergySpace lower L positive) :
    actualHighGraphKnownFunctionalValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
      (addCrossData parameters lower data cross).weighted (addCrossData parameters lower data cross).auxiliary
      (addCrossData parameters lower data cross).graphs (addCrossData parameters lower data cross).datum test =
    actualHighGraphKnownFunctionalValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
      data.weighted data.auxiliary data.graphs data.datum test +
    crossKnownValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state cross test := by
  simp only [addCrossData, actualHighGraphKnownFunctionalValue, crossKnownValue,
    actualHighKnownBulkOutput, actualHighGraphBoundaryVector, map_add, Submodule.coe_add, inner_add_right]
  ring

end Grad.AnnularFullSource
