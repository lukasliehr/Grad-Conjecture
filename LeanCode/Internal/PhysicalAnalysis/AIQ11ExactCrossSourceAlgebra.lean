import AIQ10IndependentPhysicalWeakUniqueness
import AEM24ExactGraphNativeCrossEmbedding

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularPhysicalSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularCurrentSource
open Grad.AnnularCurrentBoundary Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularCrossMaps
open Grad.ActualBoundaryInverse Grad.ActualBoundaryPrimitives

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)

theorem crossSourceGraphLift_zero :
    graphSourceBoundaryLiftOnHigh state.outerInverseState 0 0
      (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0
        (0 : HighRadialSourceGraphs parameters lower 0)) = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm
  · simpa only [Prod.fst_zero, Prod.snd_zero, norm_zero, mul_zero, add_zero] using
      highGraphSourceBoundaryLiftOnHigh_bound parameters L compact lower positive lowerHalf state.outerInverseState 0 0
        (0 : HighRadialSourceGraphs parameters lower 0)
  · exact norm_nonneg _

def crossKnownValue (data : CrossHighData parameters lower) (test : annularEnergySpace lower L positive) : ℂ :=
  inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test)
    (actualHighKnownBulkOutput parameters L compact lower positive (lowerHalf.trans (by norm_num)) state
      (crossKnownWeighted parameters lower data) (crossKnownAuxiliary parameters lower data)) -
  inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test)
    (actualBoundaryInverseOnHigh state.outerInverseState 0 0 data.ofLp.2).val

theorem crossKnownValue_literal (data : CrossHighData parameters lower) (test : annularEnergySpace lower L positive) :
    actualHighGraphKnownFunctionalValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
      (data.toGraphKnown parameters lower).weighted (data.toGraphKnown parameters lower).auxiliary
      (data.toGraphKnown parameters lower).graphs (data.toGraphKnown parameters lower).datum test =
      crossKnownValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data test := by
  change _ - inner ℂ _ (actualHighGraphBoundaryVector state.outerInverseState 0 0 data.ofLp.2
    (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 (0 : HighRadialSourceGraphs parameters lower 0))).val = _
  rw [actualHighGraphBoundaryVector, crossSourceGraphLift_zero parameters L compact lower positive lowerHalf state, add_zero]
  rfl

theorem crossKnownValue_add (first second : CrossHighData parameters lower) (test : annularEnergySpace lower L positive) :
    crossKnownValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state (first + second) test =
      crossKnownValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state first test +
      crossKnownValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state second test := by
  simp only [crossKnownValue, crossKnownWeighted_add, crossKnownAuxiliary_add, actualHighKnownBulkOutput,
    map_add, inner_add_right, WithLp.ofLp_add, Prod.snd_add, Submodule.coe_add]
  ring

theorem crossKnownValue_smul (scalar : ℂ) (data : CrossHighData parameters lower) (test : annularEnergySpace lower L positive) :
    crossKnownValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state (scalar • data) test =
      scalar * crossKnownValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data test := by
  simp only [crossKnownValue, crossKnownWeighted_smul, crossKnownAuxiliary_smul, actualHighKnownBulkOutput,
    map_smul, inner_smul_right, WithLp.ofLp_smul, Prod.smul_snd, Submodule.coe_smul]
  simp only [inner_add_right, inner_smul_right]
  ring

end Grad.AnnularPhysicalSolution
