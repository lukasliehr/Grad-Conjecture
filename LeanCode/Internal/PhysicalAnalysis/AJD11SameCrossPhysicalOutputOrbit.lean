import AJD10SameCrossEnergySmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit
open Grad.ActualBoundaryPrimitives Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource
open Grad.AnnularReconstruction Grad.AnnularKernelL2 Grad.AnnularHighInverseOrbit
open Grad.AnnularCurrentBoundary Grad.AnnularCurrentInverse Grad.AnnularPhysicalSolution Grad.AnnularCurrentSolution

attribute [local instance] Grad.AnnularCrossOrbit.crossDataNormed Grad.AnnularCrossOrbit.crossDataSeminormed
  Grad.AnnularCrossOrbit.crossDataRealInner Grad.AnnularCrossOrbit.crossDataRealNormed Grad.AnnularCrossOrbit.crossDataRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

def crossPhysicalOutputOrbit (tau : OrbitParameter) :
    CrossHighData parameters lower →L[ℂ] DivisionRow 3 lower :=
  (actualEliminatedOrbit parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 tau).comp
      ((highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength).comp
        (crossEnergyOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)) +
    crossKnownBulkOrbit parameters L compact lower positive (lowerHalf.trans (by norm_num)) state tau

theorem crossPhysicalOutputOrbit_contDiff :
    ContDiff ℝ ∞ (crossPhysicalOutputOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) := by
  exact (complexOperatorComposition_contDiff _ _
    (actualEliminatedOrbit_contDiff parameters L compact lower positive (lowerHalf.trans (by norm_num)) state)
    (complexOperatorComposition_contDiff _ _ contDiff_const
      (crossEnergyOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small))).add
    (crossKnownBulkOrbit_contDiff parameters L compact lower positive (lowerHalf.trans (by norm_num)) state)

/-- The smooth output is the literal conjugation of the original three physical outputs. -/
theorem crossPhysicalOutputOrbit_apply (tau : OrbitParameter) (datum : CrossHighData parameters lower) :
    crossPhysicalOutputOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau datum =
      orbitLpAction (RadialL2 3 lower) tau
        (crossPhysicalOutputValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
          (crossDataTranslation parameters lower (-tau) datum)) := by
  change actualEliminatedOrbit parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 tau
    (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength
      (crossEnergyOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau datum)) +
    crossKnownBulkOrbit parameters L compact lower positive (lowerHalf.trans (by norm_num)) state tau datum = _
  rw [crossEnergyOrbit_apply, crossKnownBulkOrbit_apply,
    highEightEnergyPacket_translation lower L positive parameters lengthPositive widthHalf widthLength tau,
    actualEliminatedOrbit_conjugation]
  simp only [ContinuousLinearMap.comp_apply]
  have cancel := orbitLpAction_inverse (RadialL2 8 lower) (-tau)
    (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength
      (crossEnergyValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
        (crossDataTranslation parameters lower (-tau) datum)))
  simp only [neg_neg] at cancel
  rw [cancel, ← map_add]
  rfl

end Grad.AnnularCrossOrbit
