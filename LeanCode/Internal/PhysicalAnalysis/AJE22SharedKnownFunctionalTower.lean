import AJE19SharedHighProjectionCovariance
import AJE34KnownLowBaseAndSharedBounds
import AJD8ActualKnownZeroFunctionalPullback
import AJE23FixedKnownTowerTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open scoped ContDiff
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularReconstruction
open Grad.AnnularHighInverseOrbit Grad.AnnularCrossOrbit Grad.AnnularKernelL2 Grad.AnnularCurrentEnergy
open Grad.AnnularCurrentBoundary Grad.AnnularCurrentInverse
attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  strongCarrierNormed strongCarrierSeminormed strongCarrierRealNormed strongCarrierRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

section Precomposition
variable {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def realOperatorPrecompose (input : X →L[ℝ] E) : (E →L[ℝ] F) →L[ℝ] (X →L[ℝ] F) :=
  (ContinuousLinearMap.compL ℝ X E F).flip input

theorem realOperatorPrecompose_bound (input : X →L[ℝ] E) (mapping : E →L[ℝ] F)
    (bound : ∀ source, ‖input source‖ ≤ ‖source‖) :
    ‖realOperatorPrecompose input mapping‖ ≤ ‖mapping‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg mapping)
  intro source
  exact (mapping.le_opNorm (input source)).trans
    (mul_le_mul_of_nonneg_left (bound source) (norm_nonneg mapping))
end Precomposition

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)) (state : RetainedInverseState parameters length compact)

def sharedHighKnownInput :
    StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 →L[ℝ]
      ActualHighKnownAmbient parameters lower 0 0 :=
  (ActualHighKnownCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0).subtypeL.comp
    (strongToHigh parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)

theorem sharedHighKnownInput_bound
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    ‖sharedHighKnownInput parameters lower positive lowerHalf data‖ ≤ ‖data‖ :=
  strongToHigh_bound parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data

def fullKnownFunctionalTower :
    RealOrbitTower (ActualHighKnownAmbient parameters lower 0 0 →L[ℝ] annularEnergySpace lower length positive →L[ℝ] ℝ) :=
  ⟨knownFunctionalOrbitJet parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state,
    knownFunctionalOrbitJet_hasFDerivAt parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state⟩

def sharedKnownFunctionalTower :
    RealOrbitTower (StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 →L[ℝ]
      annularEnergySpace lower length positive →L[ℝ] ℝ) :=
  (fullKnownFunctionalTower parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state).map
    (realOperatorPrecompose (sharedHighKnownInput parameters lower positive lowerHalf))

def sharedKnownFunctionalOrbitJet (angular cell : ℕ) (tau : OrbitParameter) :
    StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 →L[ℝ]
      annularEnergySpace lower length positive →L[ℝ] ℝ :=
  (sharedKnownFunctionalTower parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state).jet angular cell tau

theorem sharedKnownFunctionalOrbitJet_hasFDerivAt (angular cell : ℕ) (tau : OrbitParameter) :
    HasFDerivAt (sharedKnownFunctionalOrbitJet parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell)
      (orbitColumns
        (sharedKnownFunctionalOrbitJet parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state (angular + 1) cell tau)
        (sharedKnownFunctionalOrbitJet parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular (cell + 1) tau)) tau :=
  (sharedKnownFunctionalTower parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state).derivative angular cell tau

theorem sharedKnownFunctionalOrbitJet_contDiff (angular cell : ℕ) :
    ContDiff ℝ ∞ (sharedKnownFunctionalOrbitJet parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell) :=
  (sharedKnownFunctionalTower parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state).smooth angular cell

theorem sharedKnownFunctionalOrbitJet_bound (angular cell : ℕ) (tau : OrbitParameter) :
    ‖sharedKnownFunctionalOrbitJet parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell tau‖ ≤
      ‖knownFunctionalOrbitJet parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell tau‖ :=
  (fullKnownFunctionalTower parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state).map_bound
    (realOperatorPrecompose (sharedHighKnownInput parameters lower positive lowerHalf))
    (fun mapping => realOperatorPrecompose_bound (sharedHighKnownInput parameters lower positive lowerHalf) mapping
      (sharedHighKnownInput_bound parameters lower positive lowerHalf)) angular cell tau

def sharedKnownZeroFunctionalTower :
    RealOrbitTower (StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 →L[ℝ]
      annularInnerZero lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ) :=
  (sharedKnownFunctionalTower parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state).map
    (operatorTestRestriction (annularZeroRealInclusion lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive))

/-- Restriction is to the actual original inner-zero test graph. -/
def sharedKnownZeroFunctionalOrbitJet (angular cell : ℕ) (tau : OrbitParameter) :
    StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 →L[ℝ]
      annularInnerZero lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ :=
  (sharedKnownZeroFunctionalTower parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state).jet angular cell tau

theorem sharedKnownZeroFunctionalOrbitJet_hasFDerivAt (angular cell : ℕ) (tau : OrbitParameter) :
    HasFDerivAt (sharedKnownZeroFunctionalOrbitJet parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell)
      (orbitColumns
        (sharedKnownZeroFunctionalOrbitJet parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state (angular + 1) cell tau)
        (sharedKnownZeroFunctionalOrbitJet parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular (cell + 1) tau)) tau :=
  (sharedKnownZeroFunctionalTower parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state).derivative angular cell tau

theorem sharedKnownZeroFunctionalOrbitJet_contDiff (angular cell : ℕ) :
    ContDiff ℝ ∞ (sharedKnownZeroFunctionalOrbitJet parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell) :=
  (sharedKnownZeroFunctionalTower parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state).smooth angular cell

theorem sharedKnownFunctionalOrbitJet_apply (angular cell : ℕ) (tau : OrbitParameter)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (test : annularEnergySpace lower length positive) :
    sharedKnownFunctionalOrbitJet parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell tau data test =
      knownFunctionalOrbitJet parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell tau
        (sharedHighKnownInput parameters lower positive lowerHalf data) test := rfl

end Grad.AnnularStrongOrbit
