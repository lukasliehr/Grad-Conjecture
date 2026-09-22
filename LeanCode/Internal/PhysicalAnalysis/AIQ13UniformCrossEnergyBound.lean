import AIQ12ActualComplexLinearHighResponse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularPhysicalSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularCurrentSource
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularCrossMaps Grad.AnnularUniformBoundary
open Grad.GaugeCoefficients.Physical.Allocation

def crossResponseSize (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  1 + currentHighPrimitiveRadius parameters L compact

theorem crossResponseSize_nonnegative (parameters : PhaseParameters) (L compact : ℝ) :
    0 ≤ crossResponseSize parameters L compact := by
  have := currentHighPrimitiveRadius_positive parameters L compact
  unfold crossResponseSize
  linarith

def crossKnownConstant (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  5 * (4 * eliminatedBulkConstant parameters L compact 0 * crossResponseSize parameters L compact + 3) +
    uniformOuterTraceConstant L * knownBoundaryInverseConstant parameters L compact 1 * crossResponseSize parameters L compact

theorem crossKnownConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) :
    0 ≤ crossKnownConstant parameters L compact := by
  unfold crossKnownConstant
  have := eliminatedBulkConstant_nonnegative parameters L compact 0
  have := crossResponseSize_nonnegative parameters L compact
  have := uniformOuterTraceConstant_nonnegative L
  have := knownBoundaryInverseConstant_nonnegative parameters L compact 1
  positivity

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

include small in
theorem crossResponseSize_bounds :
    state.val.val.size 0 ≤ crossResponseSize parameters L compact ∧
      state.val.val.size 1 ≤ crossResponseSize parameters L compact := by
  constructor
  · change 1 + state.val.errorBudget 0 ≤ 1 + currentHighPrimitiveRadius parameters L compact
    exact add_le_add le_rfl ((physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon (by norm_num : 0 + 7 ≤ 1 + 7)).trans small)
  · exact add_le_add le_rfl small

include small in
theorem crossKnownSize_bound (data : CrossHighData parameters lower) :
    (data.toGraphKnown parameters lower).functionalSize parameters L compact lower state 0 0 ≤
      crossKnownConstant parameters L compact * ‖data‖ := by
  obtain ⟨size0, size1⟩ := crossResponseSize_bounds parameters L compact state small
  obtain ⟨weighted, auxiliary, datum⟩ := crossKnown_embedding_bounds parameters lower data
  have base := eliminatedBulkConstant_nonnegative parameters L compact 0
  have size := crossResponseSize_nonnegative parameters L compact
  have boundary := knownBoundaryInverseConstant_nonnegative parameters L compact 1
  have trace := uniformOuterTraceConstant_nonnegative L
  have literal : (data.toGraphKnown parameters lower).functionalSize parameters L compact lower state 0 0 =
      5 * (4 * eliminatedBulkConstant parameters L compact 0 * state.val.val.size 0 *
          ‖(data.toGraphKnown parameters lower).weighted‖ + 3 * ‖(data.toGraphKnown parameters lower).auxiliary‖) +
        uniformOuterTraceConstant L * (knownBoundaryInverseConstant parameters L compact 1 *
          state.val.val.size 1 * ‖(data.toGraphKnown parameters lower).datum‖) := by
    simp only [ActualHighGraphKnownData.functionalSize, actualHighGraphKnownFunctionalSize,
      CrossHighData.toGraphKnown, Nat.reduceAdd, Prod.fst_zero, Prod.snd_zero, norm_zero, mul_zero, add_zero]
    rfl
  rw [literal]
  calc
    _ ≤ 5 * (4 * eliminatedBulkConstant parameters L compact 0 * crossResponseSize parameters L compact * ‖data‖ + 3 * ‖data‖) +
        uniformOuterTraceConstant L * (knownBoundaryInverseConstant parameters L compact 1 * crossResponseSize parameters L compact * ‖data‖) := by
      gcongr
    _ = crossKnownConstant parameters L compact * ‖data‖ := by unfold crossKnownConstant; ring

theorem crossEnergyValue_bound (data : CrossHighData parameters lower) :
    ‖crossEnergyValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data‖ ≤
      (32 * crossKnownConstant parameters L compact) * ‖data‖ := by
  have energy := graphDataEnergySolution_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (data.toGraphKnown parameters lower)
  have source := crossKnownSize_bound parameters L compact lower state small data
  change ‖crossEnergyValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data‖ ≤
    32 * (data.toGraphKnown parameters lower).functionalSize parameters L compact lower state 0 0 +
      322 * uniformInnerLiftConstant L * ‖(0 : AnnularBoundary)‖ at energy
  simp only [norm_zero, mul_zero, add_zero] at energy
  exact energy.trans (by nlinarith)

/-- A complex continuous response to the original BF16 source subset on the one accepted B8 ball. -/
def crossEnergyResponse : CrossHighData parameters lower →L[ℂ] annularEnergySpace lower L positive :=
  (crossEnergyLinear parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small).mkContinuous
    (32 * crossKnownConstant parameters L compact)
    (crossEnergyValue_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)

end Grad.AnnularPhysicalSolution
