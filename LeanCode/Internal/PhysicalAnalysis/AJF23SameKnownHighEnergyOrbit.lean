import AJF16ExactLiftedHighOrbitIdentity
import AJE17ExactFullKnownFunctionalOrbit
import AJD8ActualKnownZeroFunctionalPullback

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularHighInverseOrbit Grad.AnnularCurrentInverse Grad.AnnularCurrentEnergy
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit Grad.AnnularReconstruction Grad.CartesianState
open Grad.AnnularOrbitGenerators Grad.AnnularInverseCalculus Grad.ClosedJets Grad.SourceCollarDivision
open Grad.AnnularCurrentSource Grad.AnnularCurrentSolution Grad.AnnularStrongOrbit Grad.AnnularCrossOrbit

attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
  (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
  (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)
  (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

/-- The complete independently prescribed known functional restricted only
to the true inner-zero test graph. -/
def knownZeroFunctionalOrbit (tau : OrbitParameter) :
    ActualHighKnownAmbient parameters lower 0 0 →L[ℝ]
      (annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ) :=
  operatorTestRestriction (annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)
    (knownFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 tau)

theorem knownZeroFunctionalOrbit_contDiff :
    ContDiff ℝ ∞ (knownZeroFunctionalOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state) :=
  operatorTestRestriction_contDiff _ _
    (knownFunctionalOrbitJet_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0)

theorem knownZeroFunctionalOrbit_translated (tau : OrbitParameter) (data : ActualHighKnownAmbient parameters lower 0 0) :
    (knownZeroFunctionalOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau data).comp
      ((zeroTestTranslation lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive tau).restrictScalars ℝ) =
    let translated := highKnownAmbientTranslation parameters lower 0 0 (-tau) data
    actualHighGraphKnownZeroFunctional parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
      translated.ofLp.1.ofLp.1 translated.ofLp.1.ofLp.2 translated.ofLp.2.ofLp.1.ofLp translated.ofLp.2.ofLp.2.ofLp.1 := by
  apply ContinuousLinearMap.ext
  intro test
  let translated := highKnownAmbientTranslation parameters lower 0 0 (-tau) data
  have pulled := knownFunctionalOrbit_pullback parameters L compact lower positive lowerHalf state lengthPositive widthHalf widthLength tau data
    (zeroTestTranslation lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive tau test).val
  have testSame : energyTranslation lower L positive (-tau)
      (zeroTestTranslation lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive tau test).val = test.val := by
    change energyTranslation lower L positive (-tau) (energyTranslation lower L positive tau test.val) = test.val
    simpa only [neg_neg] using energyTranslation_inverse lower L positive (-tau) test.val
  have literal := actualHighGraphKnownFunctional_literal parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
    translated.ofLp.1.ofLp.1 translated.ofLp.1.ofLp.2 translated.ofLp.2.ofLp.1.ofLp translated.ofLp.2.ofLp.2.ofLp.1 test.val
  have same := congrArg (fun point : annularEnergySpace lower L positive =>
    (actualHighGraphKnownFunctionalValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
      translated.ofLp.1.ofLp.1 translated.ofLp.1.ofLp.2 translated.ofLp.2.ofLp.1.ofLp translated.ofLp.2.ofLp.2.ofLp.1 point).re) testSame
  exact pulled.trans (same.trans literal.symm)

/-- Full known high energy response: the actual functional, same inverse,
and genuine incoming solver are composed once on the original carrier. -/
def knownHighEnergyOrbit (tau : OrbitParameter) :
    ActualHighKnownAmbient parameters lower 0 0 →L[ℝ] annularEnergySpace lower L positive :=
  (highSourceSolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau).comp
    (knownZeroFunctionalOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau) +
  (highIncomingSolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau).comp
    (highKnownIncomingProjection parameters lower 0 0)

theorem knownHighEnergyOrbit_contDiff :
    ContDiff ℝ ∞ (knownHighEnergyOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) :=
  (realOperatorComposition_contDiff _ _
    (highSourceSolverOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (knownZeroFunctionalOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)).add
  (realOperatorComposition_contDiff _ _
    (highIncomingSolverOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) contDiff_const)

/-- Literal conjugation of the SAME graph-native full known energy solution,
including the unchanged physical incoming normalization. -/
theorem knownHighEnergyOrbit_apply (tau : OrbitParameter) (data : ActualHighKnownAmbient parameters lower 0 0) :
    knownHighEnergyOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau data =
    let translated := highKnownAmbientTranslation parameters lower 0 0 (-tau) data
    energyTranslation lower L positive tau
      (actualHighGraphEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
        translated.ofLp.1.ofLp.1 translated.ofLp.1.ofLp.2 translated.ofLp.2.ofLp.1.ofLp
        translated.ofLp.2.ofLp.2.ofLp.1 translated.ofLp.2.ofLp.2.ofLp.2) := by
  have pulled := fullHighEnergySolverOrbit_pullback parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau
    (knownZeroFunctionalOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau data)
    (highKnownIncomingProjection parameters lower 0 0 data)
  have sourceSame := knownZeroFunctionalOrbit_translated parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau data
  let translated := highKnownAmbientTranslation parameters lower 0 0 (-tau) data
  have same := congrArg (fun source : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ =>
    energyTranslation lower L positive tau
      (currentHighLiftedSolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small source
        (physicalIncomingNormalize translated.ofLp.2.ofLp.2.ofLp.2))) sourceSame
  exact pulled.trans same

end Grad.AnnularHighGenerators
