import AJE22SharedKnownFunctionalTower

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open scoped ContDiff
namespace Grad.AnnularStrongOrbit
open Grad.AnnularReconstruction Grad.GaugeCoefficients.Physical.Allocation
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularStrongData Grad.AnnularLowEnergy Grad.AnnularKernelL2
attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  strongCarrierNormed strongCarrierSeminormed strongCarrierRealNormed strongCarrierRealModule

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact)

def fullLowDataOrbitTower : RealOrbitTower (Grad.AnnularKnownLow.KnownLowData lower →L[ℝ] LowEnergyData lower) :=
  ⟨knownLowDataOrbitJet parameters length compact lower positive bounded state,
    knownLowDataOrbitJet_hasFDerivAt parameters length compact lower positive bounded state⟩

def sharedLowDataOrbitTower :
    RealOrbitTower (StrongDataCarrier parameters lower positive bounded 0 0 →L[ℝ] LowEnergyData lower) :=
  (fullLowDataOrbitTower parameters length compact lower positive bounded state).map
    (realOperatorPrecompose (strongToLow parameters lower positive bounded 0 0))

theorem sharedLowDataOrbitTower_actual (angular cell : ℕ) (tau : OrbitParameter) :
    (sharedLowDataOrbitTower parameters length compact lower positive bounded state).jet angular cell tau =
      sharedLowDataOrbitJet parameters length compact lower positive bounded state angular cell tau := rfl

theorem sharedLowDataOrbitJet_hasFDerivAt (angular cell : ℕ) (tau : OrbitParameter) :
    HasFDerivAt (sharedLowDataOrbitJet parameters length compact lower positive bounded state angular cell)
      (Grad.AnnularHighInverseOrbit.orbitColumns
        (sharedLowDataOrbitJet parameters length compact lower positive bounded state (angular + 1) cell tau)
        (sharedLowDataOrbitJet parameters length compact lower positive bounded state angular (cell + 1) tau)) tau :=
  (sharedLowDataOrbitTower parameters length compact lower positive bounded state).derivative angular cell tau

theorem sharedLowDataOrbitJet_contDiff (angular cell : ℕ) :
    ContDiff ℝ ∞ (sharedLowDataOrbitJet parameters length compact lower positive bounded state angular cell) :=
  (sharedLowDataOrbitTower parameters length compact lower positive bounded state).smooth angular cell

end Grad.AnnularStrongOrbit
