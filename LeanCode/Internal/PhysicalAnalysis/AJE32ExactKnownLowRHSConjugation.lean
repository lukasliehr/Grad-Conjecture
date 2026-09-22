import AJE31ActualKnownLowRHSTower
import AJE15OriginalKnownBulkCovariance

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularReconstruction
open Grad.AnnularCoupledOrbit Grad.AnnularCurrentEnergy Grad.AnnularHighInverseOrbit Grad.AnnularCrossOrbit Grad.AnnularKernelL2
open Grad.AnnularKnownLow Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularLowOrbit

private theorem knownLowSeven_translation (lower : ℝ) (tau : OrbitParameter) (known : HighKnownSourceBulk lower) :
    knownLowSevenPacket lower (WithLp.toLp 2 (fun slot => orbitLpAction (RadialL2 1 lower) tau (known slot))) =
      orbitLpAction (RadialL2 7 lower) tau (knownLowSevenPacket lower known) := by
  change bulkMatrixUnit lower (4 : Fin 7) (0 : Fin 1) (orbitLpAction (RadialL2 1 lower) tau (known 0)) +
      bulkMatrixUnit lower (5 : Fin 7) (0 : Fin 1) (orbitLpAction (RadialL2 1 lower) tau (known 1)) +
      bulkMatrixUnit lower (6 : Fin 7) (0 : Fin 1) (orbitLpAction (RadialL2 1 lower) tau (known 2)) = _
  rw [sourceBulkMatrixUnit_translation,sourceBulkMatrixUnit_translation,sourceBulkMatrixUnit_translation]
  change _ = orbitLpAction (RadialL2 7 lower) tau
    (bulkMatrixUnit lower (4 : Fin 7) (0 : Fin 1) (known 0) +
      bulkMatrixUnit lower (5 : Fin 7) (0 : Fin 1) (known 1) +
      bulkMatrixUnit lower (6 : Fin 7) (0 : Fin 1) (known 2))
  simp only [map_add]

theorem knownLowSourceInput_translation (lower : ℝ) (tau : OrbitParameter) (data : KnownLowData lower) :
    knownLowSourceInput lower (knownLowInputTranslation lower tau data) =
      orbitLpAction (RadialL2 7 lower) tau (knownLowSourceInput lower data) :=
  knownLowSeven_translation lower tau data.ofLp.1.ofLp.1

theorem knownLowDirectInput_translation (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (tau : OrbitParameter) (data : KnownLowData lower) :
    knownLowDirectInput parameters lower length positive (knownLowInputTranslation lower tau data) =
      lowBulkTranslation lower tau (knownLowDirectInput parameters lower length positive data) := by
  change lowFirstOutput parameters lower length (orbitLpAction (RadialL2 1 lower) tau (data.ofLp.1.ofLp.1 3)) -
    lowAngularOutput lower length positive (radialRadiusRow lower positive
      (orbitLpAction (RadialL2 1 lower) tau data.ofLp.1.ofLp.2)) = _
  rw [lowFirstOutput_translation,radialRadiusRow_translation,lowAngularOutput_translation,← map_sub]
  rfl

theorem knownLowOutput_translation (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (row : Fin 3) (tau : OrbitParameter) (field : DivisionRow 1 lower) :
    knownLowOutput parameters length lower positive row (orbitLpAction (RadialL2 1 lower) tau field) =
      lowBulkTranslation lower tau (knownLowOutput parameters length lower positive row field) := by
  fin_cases row
  · exact lowFirstOutput_translation parameters lower length tau field
  · exact lowCellOutput_translation lower length positive tau field
  · exact lowAngularOutput_translation lower length positive tau field

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (state : RetainedInverseState parameters length compact)

theorem knownLowRowOperatorJet_zero_apply (row : Fin 3) (tau : OrbitParameter) (data : KnownLowData lower) :
    knownLowRowOperatorJet parameters length compact lower positive bounded state row 0 0 tau data =
      knownLowBulkIntoData lower (knownLowOutput parameters length lower positive row
        (actualLowRowOrbit parameters length compact lower positive bounded state row tau (knownLowSourceInput lower data))) := by
  unfold knownLowRowOperatorJet actualLowRowOrbitJet
  rw [radialOrbitJetAction_zero]
  rfl

theorem knownLowDataOrbitJet_bulk (tau : OrbitParameter) (data : KnownLowData lower) :
    (knownLowDataOrbitJet parameters length compact lower positive bounded state 0 0 tau data).ofLp.1 =
      knownLowOutput parameters length lower positive 0
        (actualLowRowOrbit parameters length compact lower positive bounded state 0 tau (knownLowSourceInput lower data)) +
      knownLowOutput parameters length lower positive 1
        (actualLowRowOrbit parameters length compact lower positive bounded state 1 tau (knownLowSourceInput lower data)) +
      knownLowOutput parameters length lower positive 2
        (actualLowRowOrbit parameters length compact lower positive bounded state 2 tau (knownLowSourceInput lower data)) +
      knownLowDirectInput parameters lower length positive data := by
  unfold knownLowDataOrbitJet
  simp only [add_apply,knownLowRowOperatorJet_zero_apply]
  rfl

theorem knownLowDataOrbitJet_incoming (tau : OrbitParameter) (data : KnownLowData lower) :
    (knownLowDataOrbitJet parameters length compact lower positive bounded state 0 0 tau data).ofLp.2 = data.ofLp.2 := by
  unfold knownLowDataOrbitJet
  simp only [add_apply,knownLowRowOperatorJet_zero_apply]
  change 0 + 0 + 0 + data.ofLp.2 = data.ofLp.2
  simp only [zero_add]

private theorem knownLowRow_conjugation (row : Fin 3) (tau : OrbitParameter) (data : KnownLowData lower) :
    knownLowOutput parameters length lower positive row
      (actualLowRowOrbit parameters length compact lower positive bounded state row tau (knownLowSourceInput lower data)) =
    lowBulkTranslation lower tau
      (knownLowOutput parameters length lower positive row
        (lowPhysicalRowAction parameters length compact lower positive bounded state row
          (knownLowSourceInput lower (knownLowInputTranslation lower (-tau) data)))) := by
  rw [actualLowRowOrbit_conjugation]
  change knownLowOutput parameters length lower positive row
    (orbitLpAction (RadialL2 1 lower) tau (lowPhysicalRowAction parameters length compact lower positive bounded state row
      (orbitLpAction (RadialL2 7 lower) (-tau) (knownLowSourceInput lower data)))) = _
  rw [knownLowOutput_translation,knownLowSourceInput_translation]

private theorem splitSourceSum {E : Type*} [AddCommGroup E] (a b c d e : E) :
    (a + b) + c + (d - e) = a + c + d + (b - e) := by abel

private theorem knownLowForcing_split (data : KnownLowData lower) :
    knownLowForcing parameters length compact lower positive bounded state data.ofLp.1.ofLp.1 data.ofLp.1.ofLp.2 =
      knownLowOutput parameters length lower positive 0
        (lowPhysicalRowAction parameters length compact lower positive bounded state 0 (knownLowSourceInput lower data)) +
      knownLowOutput parameters length lower positive 1
        (lowPhysicalRowAction parameters length compact lower positive bounded state 1 (knownLowSourceInput lower data)) +
      knownLowOutput parameters length lower positive 2
        (lowPhysicalRowAction parameters length compact lower positive bounded state 2 (knownLowSourceInput lower data)) +
      knownLowDirectInput parameters lower length positive data := by
  unfold knownLowForcing
  rw [map_add,map_sub]
  exact splitSourceSum _ _ _ _ _

/-- Exact real operator orbit of the SAME AIR data map, with true source
translation and original independently prescribed incoming value. -/
theorem knownLowDataOrbit_apply (tau : OrbitParameter) (data : KnownLowData lower) :
    knownLowDataOrbitJet parameters length compact lower positive bounded state 0 0 tau data =
      lowDataTranslationEquivalence lower tau
        (knownLowDataMap parameters length compact lower positive bounded state (knownLowInputTranslation lower (-tau) data)) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
  apply Prod.ext
  · change (knownLowDataOrbitJet parameters length compact lower positive bounded state 0 0 tau data).ofLp.1 =
      (lowDataTranslationEquivalence lower tau
        (knownLowDataMap parameters length compact lower positive bounded state (knownLowInputTranslation lower (-tau) data))).ofLp.1
    rw [knownLowDataOrbitJet_bulk]
    rw [knownLowRow_conjugation,knownLowRow_conjugation,knownLowRow_conjugation]
    have direct := congrArg (lowBulkTranslation lower tau)
      (knownLowDirectInput_translation parameters lower length positive (-tau) data)
    rw [lowBulkTranslation_inverse] at direct
    rw [← direct,← map_add,← map_add,← map_add]
    change lowBulkTranslation lower tau _ = lowBulkTranslation lower tau
      (knownLowForcing parameters length compact lower positive bounded state
        (knownLowInputTranslation lower (-tau) data).ofLp.1.ofLp.1
        (knownLowInputTranslation lower (-tau) data).ofLp.1.ofLp.2)
    exact congrArg (lowBulkTranslation lower tau)
      (knownLowForcing_split parameters length compact lower positive bounded state (knownLowInputTranslation lower (-tau) data)).symm
  · change (knownLowDataOrbitJet parameters length compact lower positive bounded state 0 0 tau data).ofLp.2 =
      (lowDataTranslationEquivalence lower tau
        (knownLowDataMap parameters length compact lower positive bounded state (knownLowInputTranslation lower (-tau) data))).ofLp.2
    rw [knownLowDataOrbitJet_incoming]
    change data.ofLp.2 = lowBoundaryTranslation tau (lowBoundaryTranslation (-tau) data.ofLp.2)
    exact (lowBoundaryTranslation_inverse tau data.ofLp.2).symm

end Grad.AnnularStrongOrbit
