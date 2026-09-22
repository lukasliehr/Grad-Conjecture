import AJE16FullKnownFunctionalTower

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularReconstruction
open Grad.AnnularHighInverseOrbit Grad.AnnularCrossOrbit Grad.AnnularKernelL2 Grad.AnnularCurrentEnergy Grad.AnnularCurrentBoundary
open Grad.ActualBoundaryInverse Grad.AnnularCoupledOrbit
attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule

private theorem sumConjugation {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (forward backward : F →L[ℂ] F) (input : E →L[ℂ] E) (mapping shifted : E →L[ℂ] F)
    (source shiftedSource : E) (direct shiftedDirect : F)
    (same : shifted = forward.comp (mapping.comp input))
    (sourceSame : shiftedSource = input source) (directSame : shiftedDirect = backward direct)
    (inverse : forward (backward direct) = direct) :
    shifted source + direct = forward (mapping shiftedSource + shiftedDirect) := by
  rw [same,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,sourceSame,directSame,map_add,inverse]

private theorem boundaryConjugation (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (tau : OrbitParameter)
    (datum : HighBoundaryPrimitive parameters 0 0) (source : SourceBoundaryTuple) :
    actualBoundaryInverseOrbitJet parameters L compact state 0 0 tau datum +
      graphSourceLiftOrbitJet parameters L compact state.outerInverseState 0 0 0 0 tau source =
    orbitLpAction (ComplexEuclidean 1) tau
      (actualHighGraphBoundaryVector state.outerInverseState 0 0
        (highBoundaryTranslation parameters (-tau) datum) (sourceTupleTranslation (-tau) source)).val := by
  rw [actualBoundaryInverseOrbit_apply,graphSourceLiftOrbit_apply,← map_add]
  rfl

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (state : RetainedInverseState parameters L compact)

theorem knownBulkOrbitJet_zero_apply (tau : OrbitParameter) (data : ActualHighKnownAmbient parameters lower 0 0) :
    knownBulkOrbitJet parameters L compact lower positive lowerHalf state 0 0 tau data =
      actualEliminatedOrbit parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 tau
        (knownAmbientEight parameters lower 0 0 data) + knownAmbientDirect parameters lower 0 0 positive data := by
  unfold knownBulkOrbitJet actualEliminatedOrbitJet
  rw [radialOrbitJetAction_zero]
  rfl

/-- Actual full known output, with the same original source translated
in every row and no change to the coefficient state. -/
theorem knownBulkOrbit_apply (tau : OrbitParameter) (data : ActualHighKnownAmbient parameters lower 0 0) :
    knownBulkOrbitJet parameters L compact lower positive lowerHalf state 0 0 tau data =
      orbitLpAction (RadialL2 3 lower) tau
        (actualHighKnownBulkOutput parameters L compact lower positive (lowerHalf.trans (by norm_num)) state
          (highKnownAmbientTranslation parameters lower 0 0 (-tau) data).ofLp.1.ofLp.1
          (highKnownAmbientTranslation parameters lower 0 0 (-tau) data).ofLp.1.ofLp.2) := by
  exact (knownBulkOrbitJet_zero_apply parameters L compact lower positive lowerHalf state tau data).trans
    (sumConjugation
      (orbitLpAction (RadialL2 3 lower) tau) (orbitLpAction (RadialL2 3 lower) (-tau))
      (orbitLpAction (RadialL2 8 lower) (-tau))
      (eliminatedBulkAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0)
      (actualEliminatedOrbit parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 tau)
      (knownAmbientEight parameters lower 0 0 data)
      (knownAmbientEight parameters lower 0 0 (highKnownAmbientTranslation parameters lower 0 0 (-tau) data))
      (knownAmbientDirect parameters lower 0 0 positive data)
      (knownAmbientDirect parameters lower 0 0 positive (highKnownAmbientTranslation parameters lower 0 0 (-tau) data))
      (actualEliminatedOrbit_conjugation parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 tau)
      (knownAmbientEight_translation parameters lower (-tau) data)
      (knownAmbientDirect_translation parameters lower positive (-tau) data)
      (orbitLpAction_inverse (RadialL2 3 lower) tau (knownAmbientDirect parameters lower 0 0 positive data)))

/-- Actual beta inverse plus the actual -T^-1 H source lift on the same
three genuine graph traces. -/
theorem knownBoundaryOrbit_apply (tau : OrbitParameter) (data : ActualHighKnownAmbient parameters lower 0 0) :
    knownBoundaryOrbitJet parameters L compact lower positive lowerHalf state 0 0 tau data =
      orbitLpAction (ComplexEuclidean 1) tau
        (actualHighGraphBoundaryVector state.outerInverseState 0 0
          (highKnownDatumProjection parameters lower 0 0 (highKnownAmbientTranslation parameters lower 0 0 (-tau) data))
          (knownAmbientSourceTuple parameters lower 0 0 positive (lowerHalf.trans_lt (by norm_num))
            (highKnownAmbientTranslation parameters lower 0 0 (-tau) data))).val := by
  change actualBoundaryInverseOrbitJet parameters L compact state 0 0 tau
      (highKnownDatumProjection parameters lower 0 0 data) +
    graphSourceLiftOrbitJet parameters L compact state.outerInverseState 0 0 0 0 tau
      (knownAmbientSourceTuple parameters lower 0 0 positive (lowerHalf.trans_lt (by norm_num)) data) = _
  have sourceSame := knownAmbientSourceTuple_translation parameters lower 0 0 positive
    (lowerHalf.trans_lt (by norm_num)) (-tau) data
  exact (boundaryConjugation parameters L compact state tau
    (highKnownDatumProjection parameters lower 0 0 data)
    (knownAmbientSourceTuple parameters lower 0 0 positive (lowerHalf.trans_lt (by norm_num)) data)).trans
      (congrArg (fun source : SourceBoundaryTuple =>
        orbitLpAction (ComplexEuclidean 1) tau
          (actualHighGraphBoundaryVector state.outerInverseState 0 0
            (highBoundaryTranslation parameters (-tau) (highKnownDatumProjection parameters lower 0 0 data)) source).val)
        sourceSame.symm)

variable (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))

/-- Exact pullback identity for AEK12's complete genuine known functional.
The same translated datum and the same translated physical test occur. -/
theorem knownFunctionalOrbit_pullback (tau : OrbitParameter) (data : ActualHighKnownAmbient parameters lower 0 0)
    (test : annularEnergySpace lower L positive) :
    knownFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 tau data test =
      (actualHighGraphKnownFunctionalValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
        (highKnownAmbientTranslation parameters lower 0 0 (-tau) data).ofLp.1.ofLp.1
        (highKnownAmbientTranslation parameters lower 0 0 (-tau) data).ofLp.1.ofLp.2
        (highKnownAmbientTranslation parameters lower 0 0 (-tau) data).ofLp.2.ofLp.1.ofLp
        (highKnownAmbientTranslation parameters lower 0 0 (-tau) data).ofLp.2.ofLp.2.ofLp.1
        (energyTranslation lower L positive (-tau) test)).re := by
  let translated := highKnownAmbientTranslation parameters lower 0 0 (-tau) data
  let bulk := actualHighKnownBulkOutput parameters L compact lower positive
    (lowerHalf.trans (by norm_num)) state translated.ofLp.1.ofLp.1 translated.ofLp.1.ofLp.2
  let boundary := (actualHighGraphBoundaryVector state.outerInverseState 0 0
    (highKnownDatumProjection parameters lower 0 0 translated)
    (knownAmbientSourceTuple parameters lower 0 0 positive (lowerHalf.trans_lt (by norm_num)) translated)).val
  have bulkEquality : inner ℂ
      (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test)
      (knownBulkOrbitJet parameters L compact lower positive lowerHalf state 0 0 tau data) =
    inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength
      (energyTranslation lower L positive (-tau) test)) bulk := by
    exact (congrArg (fun output : DivisionRow 3 lower => inner ℂ
      (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test) output)
      (knownBulkOrbit_apply parameters L compact lower positive lowerHalf state tau data)).trans
        ((orbitLp_inner_move tau _ bulk).trans
          (congrArg (fun packet : DivisionRow 3 lower => inner ℂ packet bulk)
            (highEnergyTestPacket_translation lower L positive parameters lengthPositive widthHalf widthLength (-tau) test).symm))
  have boundaryEquality : inner ℂ
      (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test)
      (knownBoundaryOrbitJet parameters L compact lower positive lowerHalf state 0 0 tau data) =
    inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0
      (energyTranslation lower L positive (-tau) test)) boundary := by
    exact (congrArg (fun output : NegativeTrace parameters 0 0 1 => inner ℂ
      (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test) output)
      (knownBoundaryOrbit_apply parameters L compact lower positive lowerHalf state tau data)).trans
        ((orbitLp_inner_move tau _ boundary).trans
          (congrArg (fun packet : PositiveTrace parameters 0 0 1 => inner ℂ packet boundary)
            (actualOuterTrace_translation parameters lower L positive lowerHalf lengthPositive 0 0 (-tau) test).symm))
  have literal := (knownFunctionalOrbitJet_literal parameters L compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state 0 0 tau data test).trans
      (congrArg (fun pair : ℂ => pair.re) (congrArg₂ (fun first second : ℂ => first - second)
        bulkEquality boundaryEquality))
  have sourceSame := knownAmbientSourceTuple_apply parameters lower 0 0 positive
    (lowerHalf.trans_lt (by norm_num)) translated
  dsimp only [boundary] at literal
  rw [sourceSame] at literal
  exact literal

end Grad.AnnularStrongOrbit
