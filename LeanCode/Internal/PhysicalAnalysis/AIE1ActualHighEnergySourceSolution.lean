import AEL9SamePhysicalDiagonalConsumer
import AEK5ActualKnownFunctional

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
theorem actualHighKnownFunctionalValue_test_smul (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact) (angular cell : ℕ)
    (known : HighKnownSourceBulk lower) (auxiliary : HighAuxiliarySourceBulk lower)
    (datum : HighBoundaryPrimitive parameters angular cell) (source : ZAmbient parameters (angular + cell + 2))
    (scalar : ℂ) (test : annularEnergySpace lower L positive) :
    actualHighKnownFunctionalValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength
      state angular cell known auxiliary datum source (scalar • test) =
    starRingEnd ℂ scalar * actualHighKnownFunctionalValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength
      state angular cell known auxiliary datum source test := by
  simp only [actualHighKnownFunctionalValue, map_smul, inner_smul_left]
  ring

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)
    (known : HighKnownSourceBulk lower) (auxiliary : HighAuxiliarySourceBulk lower)
    (datum : HighBoundaryPrimitive parameters 0 0) (source : ZAmbient parameters 2)
    (innerValue : AnnularBoundary)

/-- The actual base high energy solution for all independently weighted known
bulk entries and the SAME original affine outer boundary term. -/
def actualHighEnergySolution : annularEnergySpace lower L positive :=
  currentHighLiftedSolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (actualHighKnownZeroFunctional parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
      known auxiliary datum source) innerValue

theorem actualHighEnergySolution_inner :
    annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (actualHighEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small known auxiliary datum source innerValue) = innerValue :=
  currentHighLiftedSolution_inner parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small _ innerValue

theorem actualHighEnergySolution_complex
    (test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
    currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (actualHighEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small known auxiliary datum source innerValue) test.val =
    actualHighKnownFunctionalValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
      known auxiliary datum source test.val := by
  apply currentHighLiftedSolution_complex parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (actualHighKnownZeroFunctional parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 known auxiliary datum source)
    (actualHighKnownFunctionalValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 known auxiliary datum source)
  · intro point
    exact actualHighKnownFunctional_literal parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
      known auxiliary datum source point.val
  · intro point
    exact actualHighKnownFunctionalValue_test_smul parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
      known auxiliary datum source Complex.I point

theorem actualHighEnergySolution_unique
    (candidate : annularEnergySpace lower L positive)
    (innerLaw : annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0 candidate = innerValue)
    (equation : ∀ test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive,
      currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state candidate test.val =
        actualHighKnownFunctionalValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 known auxiliary datum source test.val) :
    candidate = actualHighEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small known auxiliary datum source innerValue := by
  apply currentHighLiftedSolution_complex_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (actualHighKnownZeroFunctional parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 known auxiliary datum source)
    (actualHighKnownFunctionalValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 known auxiliary datum source)
    _ innerValue candidate innerLaw equation
  intro point
  exact actualHighKnownFunctional_literal parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
    known auxiliary datum source point.val

end Grad.AnnularCurrentSolution
