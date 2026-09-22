import AIE4ActualGraphSourceEnergySolution
import AEK14GraphKnownDataConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularCurrentSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularCurrentSource
open Grad.AnnularKernelL2 Grad.AnnularCurrentBoundary Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives
open Grad.RealFixedRanges Grad.AxisCore Grad.SourceBoundaryTrace Grad.AnnularTiltedReference Grad.AnnularUniformBoundary

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)
    (data : ActualHighGraphKnownData parameters lower 0 0)

/-- The actual current solution for a coherent original BF2 source packet. -/
def graphDataEnergySolution : annularEnergySpace lower L positive :=
  actualHighGraphEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength
    state small data.weighted data.auxiliary data.graphs data.datum data.innerValue

/-- The incoming datum is the sharp trace of the physical decoded field. -/
theorem graphDataEnergySolution_physical_inner :
    annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (bEnergyDecode lower L positive
        (graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)) = data.innerValue := by
  rw [physicalIncomingTrace_iff]
  exact actualHighGraphEnergySolution_inner parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength
    state small data.weighted data.auxiliary data.graphs data.datum data.innerValue

/-- Uniform BF13 energy estimate, using independent weighted bulk and genuine
source graph norms.  Every coefficient is independent of the inner radius. -/
theorem graphDataEnergySolution_bound :
    ‖graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data‖ ≤
      32 * data.functionalSize parameters L compact lower state 0 0 +
        322 * uniformInnerLiftConstant L * ‖data.innerValue‖ := by
  have solution := currentHighLiftedSolution_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength
    state small (data.zeroFunctional parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0)
    (physicalIncomingNormalize data.innerValue)
  have source := data.zeroFunctional_norm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
  have incoming := physicalIncomingNormalize_bound data.innerValue
  have liftPositive : 0 ≤ uniformInnerLiftConstant L := Real.sqrt_nonneg _
  change ‖graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data‖ ≤ _ at solution
  exact solution.trans (by nlinarith)

/-- Literal full three-row law for the SAME constructed solution. -/
theorem graphDataEnergySolution_full_packet
    (test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
    let field := graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
    inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test.val)
      (actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field data.weighted data.auxiliary) =
    inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test.val)
      ((actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf lengthPositive 0 0 state.outerInverseState field).val +
        (actualHighGraphBoundaryVector state.outerInverseState 0 0 data.datum
          (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 data.graphs)).val) := by
  dsimp only
  apply actualFullHighOutput_variational parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
  exact actualHighGraphEnergySolution_complex parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength
    state small data.weighted data.auxiliary data.graphs data.datum data.innerValue test

/-- The actual compact-testing input needed to recover the genuine Domega
flux graph; only the test's true outer trace is set to zero. -/
theorem graphDataEnergySolution_zeroOuter
    (test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)
    (outerZero : actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test.val = 0) :
    inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test.val)
      (actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
        (graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
        data.weighted data.auxiliary) = 0 := by
  have law := graphDataEnergySolution_full_packet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data test
  dsimp only at law
  rw [outerZero, inner_zero_left] at law
  exact law

/-- Arbitrary physical-incoming variational solutions equal this SAME field. -/
theorem graphDataEnergySolution_unique
    (candidate : annularEnergySpace lower L positive)
    (incoming : annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (bEnergyDecode lower L positive candidate) = data.innerValue)
    (equation : ∀ test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive,
      currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state candidate test.val =
        actualHighGraphKnownFunctionalValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
          data.weighted data.auxiliary data.graphs data.datum test.val) :
    candidate = graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data := by
  apply actualHighGraphEnergySolution_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    data.weighted data.auxiliary data.graphs data.datum data.innerValue candidate
  · exact (physicalIncomingTrace_iff lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive candidate data.innerValue).mp incoming
  · exact equation

end Grad.AnnularCurrentSolution
