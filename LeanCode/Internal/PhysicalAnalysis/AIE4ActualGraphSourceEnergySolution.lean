import AIE3PhysicalIncomingNormalization
import AEK12GraphNativeKnownFunctional

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularCurrentSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularCurrentSource
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.RealFixedRanges Grad.AxisCore Grad.SourceBoundaryTrace

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

/-- The actual known complex functional is conjugate linear in its test. -/
theorem actualHighGraphKnownFunctionalValue_test_smul (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact) (angular cell : ℕ)
    (known : HighKnownSourceBulk lower) (auxiliary : HighAuxiliarySourceBulk lower)
    (graphs : HighRadialSourceGraphs parameters lower (angular + cell)) (datum : HighBoundaryPrimitive parameters angular cell)
    (scalar : ℂ) (test : annularEnergySpace lower L positive) :
    actualHighGraphKnownFunctionalValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength
      state angular cell known auxiliary graphs datum (scalar • test) =
    starRingEnd ℂ scalar * actualHighGraphKnownFunctionalValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength
      state angular cell known auxiliary graphs datum test := by
  simp only [actualHighGraphKnownFunctionalValue, map_smul, inner_smul_left]
  ring

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)
    (known : HighKnownSourceBulk lower) (auxiliary : HighAuxiliarySourceBulk lower)
    (graphs : HighRadialSourceGraphs parameters lower 0) (datum : HighBoundaryPrimitive parameters 0 0)
    (innerValue : AnnularBoundary)

/-- The actual base high energy solution for all independently weighted known
bulk entries and genuine original radial-graph outer sources and physical incoming datum. -/
def actualHighGraphEnergySolution : annularEnergySpace lower L positive :=
  currentHighLiftedSolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (actualHighGraphKnownZeroFunctional parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
      known auxiliary graphs datum) (physicalIncomingNormalize innerValue)

theorem actualHighGraphEnergySolution_inner :
    annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (actualHighGraphEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small known auxiliary graphs datum innerValue) = physicalIncomingNormalize innerValue :=
  currentHighLiftedSolution_inner parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small _ (physicalIncomingNormalize innerValue)

theorem actualHighGraphEnergySolution_complex
    (test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
    currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (actualHighGraphEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small known auxiliary graphs datum innerValue) test.val =
    actualHighGraphKnownFunctionalValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
      known auxiliary graphs datum test.val := by
  apply currentHighLiftedSolution_complex parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (actualHighGraphKnownZeroFunctional parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 known auxiliary graphs datum)
    (actualHighGraphKnownFunctionalValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 known auxiliary graphs datum)
  · intro point
    exact actualHighGraphKnownFunctional_literal parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
      known auxiliary graphs datum point.val
  · intro point
    exact actualHighGraphKnownFunctionalValue_test_smul parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
      known auxiliary graphs datum Complex.I point

theorem actualHighGraphEnergySolution_unique
    (candidate : annularEnergySpace lower L positive)
    (innerLaw : annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0 candidate = physicalIncomingNormalize innerValue)
    (equation : ∀ test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive,
      currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state candidate test.val =
        actualHighGraphKnownFunctionalValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 known auxiliary graphs datum test.val) :
    candidate = actualHighGraphEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small known auxiliary graphs datum innerValue := by
  apply currentHighLiftedSolution_complex_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (actualHighGraphKnownZeroFunctional parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 known auxiliary graphs datum)
    (actualHighGraphKnownFunctionalValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 known auxiliary graphs datum)
    _ (physicalIncomingNormalize innerValue) candidate innerLaw equation
  intro point
  exact actualHighGraphKnownFunctional_literal parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
    known auxiliary graphs datum point.val

end Grad.AnnularCurrentSolution
