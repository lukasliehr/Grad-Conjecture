import AJF23SameKnownHighEnergyOrbit

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
open Grad.AnnularCurrentSource Grad.AnnularCurrentSolution Grad.AnnularStrongOrbit Grad.AnnularCrossOrbit Grad.AnnularKernelL2

attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
  (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
  (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)
  (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

/-- The literal physical eight-input energy packet followed by the actual
elimination operator, on the original real energy carrier. -/
def energyPhysicalOutputOrbit (tau : OrbitParameter) :
    annularEnergySpace lower L positive →L[ℝ] DivisionRow 3 lower :=
  realInputPrecompose ((highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength).restrictScalars ℝ)
    (actualEliminatedOrbit parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 tau)

theorem energyPhysicalOutputOrbit_contDiff :
    ContDiff ℝ ∞ (energyPhysicalOutputOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state) := by
  have composed := (ContinuousLinearMap.contDiff (𝕜 := ℝ)
    (E := DivisionRow 8 lower →L[ℂ] DivisionRow 3 lower)
    (F := annularEnergySpace lower L positive →L[ℝ] DivisionRow 3 lower)
    (realInputPrecompose ((highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength).restrictScalars ℝ))).comp
    (actualEliminatedOrbit_contDiff parameters L compact lower positive (lowerHalf.trans (by norm_num)) state)
  exact composed

theorem energyPhysicalOutputOrbit_translated (tau : OrbitParameter) (field : annularEnergySpace lower L positive) :
    energyPhysicalOutputOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau
      (energyTranslation lower L positive tau field) =
    orbitLpAction (RadialL2 3 lower) tau
      (eliminatedBulkAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
        (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength field)) := by
  change actualEliminatedOrbit parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 tau
    (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength
      (energyTranslation lower L positive tau field)) = _
  rw [highEightEnergyPacket_translation lower L positive parameters lengthPositive widthHalf widthLength tau,
    actualEliminatedOrbit_conjugation]
  simp only [ContinuousLinearMap.comp_apply]
  have cancel := orbitLpAction_inverse (RadialL2 8 lower) (-tau)
    (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength field)
  simp only [neg_neg] at cancel
  exact congrArg (fun packet : DivisionRow 8 lower => orbitLpAction (RadialL2 3 lower) tau
    (eliminatedBulkAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 packet)) cancel

/-- Full physical output uses that same energy solution and all prescribed
known/direct rows exactly once. -/
def knownPhysicalOutputOrbit (tau : OrbitParameter) :
    ActualHighKnownAmbient parameters lower 0 0 →L[ℝ] DivisionRow 3 lower :=
  (energyPhysicalOutputOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau).comp
    (knownHighEnergyOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau) +
    knownBulkOrbitJet parameters L compact lower positive lowerHalf state 0 0 tau

theorem knownPhysicalOutputOrbit_contDiff :
    ContDiff ℝ ∞ (knownPhysicalOutputOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) :=
  (realOperatorComposition_contDiff _ _
    (energyPhysicalOutputOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    (knownHighEnergyOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)).add
    (knownBulkOrbitJet_contDiff parameters L compact lower positive lowerHalf state 0 0)

/-- Literal conjugation of the SAME actual full three-output packet. -/
theorem knownPhysicalOutputOrbit_apply (tau : OrbitParameter) (data : ActualHighKnownAmbient parameters lower 0 0) :
    knownPhysicalOutputOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau data =
    let translated := highKnownAmbientTranslation parameters lower 0 0 (-tau) data
    orbitLpAction (RadialL2 3 lower) tau
      (actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
        (actualHighGraphEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
          translated.ofLp.1.ofLp.1 translated.ofLp.1.ofLp.2 translated.ofLp.2.ofLp.1.ofLp
          translated.ofLp.2.ofLp.2.ofLp.1 translated.ofLp.2.ofLp.2.ofLp.2)
        translated.ofLp.1.ofLp.1 translated.ofLp.1.ofLp.2) := by
  let translated := highKnownAmbientTranslation parameters lower 0 0 (-tau) data
  let field := actualHighGraphEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    translated.ofLp.1.ofLp.1 translated.ofLp.1.ofLp.2 translated.ofLp.2.ofLp.1.ofLp
    translated.ofLp.2.ofLp.2.ofLp.1 translated.ofLp.2.ofLp.2.ofLp.2
  have energy := (congrArg
    (energyPhysicalOutputOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau)
    (knownHighEnergyOrbit_apply parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau data)).trans
    (energyPhysicalOutputOrbit_translated parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau field)
  have known := knownBulkOrbit_apply parameters L compact lower positive lowerHalf state tau data
  have added := congrArg₂ (fun first second : DivisionRow 3 lower => first + second) energy known
  exact added.trans (map_add (orbitLpAction (RadialL2 3 lower) tau) _ _).symm

end Grad.AnnularHighGenerators
