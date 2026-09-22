import AJE33KnownLowRHSOneHigh
import AJE14CompleteKnownCoefficientTower

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource Grad.AnnularCurrentEnergy
open Grad.AnnularStrongData Grad.AnnularReconstruction Grad.AnnularHighInverseOrbit Grad.AnnularKernelL2
open Grad.AnnularKnownLow Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularLowOrbit Grad.AnnularCoupledOrbit
open Grad.GaugeCoefficients.Physical.Allocation

local instance strongCarrierNormed (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) : NormedAddCommGroup (StrongDataCarrier parameters lower positive bounded 0 0) := inferInstance
local instance strongCarrierSeminormed (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) : SeminormedAddCommGroup (StrongDataCarrier parameters lower positive bounded 0 0) :=
  (strongCarrierNormed parameters lower positive bounded).toSeminormedAddCommGroup
local instance strongCarrierRealNormed (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) : NormedSpace ℝ (StrongDataCarrier parameters lower positive bounded 0 0) := by
  letI : NormedSpace ℝ (ActualHighKnownAmbient parameters lower 0 0) := knownAmbientRealNormed parameters lower
  letI : NormedSpace ℝ (StrongDataAmbient parameters lower 0 0) := inferInstance
  exact inferInstance
local instance strongCarrierRealModule (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) : Module ℝ (StrongDataCarrier parameters lower positive bounded 0 0) :=
  (strongCarrierRealNormed parameters lower positive bounded).toModule

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (state : RetainedInverseState parameters length compact)

def knownLowBaseConstant : ℝ :=
  2 * knownLowSourceConstant parameters length compact + lowBalanceConstant length parameters.gamma + 5

theorem knownLowBaseConstant_nonnegative : 0 ≤ knownLowBaseConstant parameters length compact := by
  have source := knownLowSourceConstant_nonnegative parameters length compact
  have balance : 1 ≤ lowBalanceConstant length parameters.gamma := le_max_left _ _
  unfold knownLowBaseConstant
  linarith

/-- The full original AIR RHS has a uniform base bound on the unchanged B8 ball. -/
theorem knownLowDataOrbitJet_base_bound
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ 1)
    (tau : OrbitParameter) :
    ‖knownLowDataOrbitJet parameters length compact lower positive bounded state 0 0 tau‖ ≤
      knownLowBaseConstant parameters length compact := by
  apply ContinuousLinearMap.opNorm_le_bound _ (knownLowBaseConstant_nonnegative parameters length compact)
  intro data
  rw [knownLowDataOrbit_apply parameters length compact lower positive bounded state tau data,
    (lowDataTranslationEquivalence lower tau).norm_map]
  exact ((knownLowDataMap parameters length compact lower positive bounded state).le_opNorm
    (knownLowInputTranslation lower (-tau) data)).trans
      ((mul_le_mul_of_nonneg_right
        (knownLowDataMap_uniform parameters length compact lower positive bounded state small)
        (norm_nonneg (knownLowInputTranslation lower (-tau) data))).trans_eq
          (congrArg (fun size : ℝ => knownLowBaseConstant parameters length compact * size)
            ((knownLowInputTranslation lower (-tau)).norm_map data)))

/-- The same once-prescribed strong datum supplies every actual low forcing jet. -/
def sharedLowDataOrbitJet (angular cell : ℕ) (tau : OrbitParameter) :
    StrongDataCarrier parameters lower positive bounded 0 0 →L[ℝ] LowEnergyData lower :=
  (knownLowDataOrbitJet parameters length compact lower positive bounded state angular cell tau).comp
    (strongToLow parameters lower positive bounded 0 0)

theorem sharedLowDataOrbitJet_apply (angular cell : ℕ) (tau : OrbitParameter)
    (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    sharedLowDataOrbitJet parameters length compact lower positive bounded state angular cell tau data =
      knownLowDataOrbitJet parameters length compact lower positive bounded state angular cell tau
        (strongToLow parameters lower positive bounded 0 0 data) := rfl

theorem sharedLowDataOrbitJet_bound (angular cell : ℕ) (tau : OrbitParameter) :
    ‖sharedLowDataOrbitJet parameters length compact lower positive bounded state angular cell tau‖ ≤
      ‖knownLowDataOrbitJet parameters length compact lower positive bounded state angular cell tau‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro data
  exact ((knownLowDataOrbitJet parameters length compact lower positive bounded state angular cell tau).le_opNorm
    (strongToLow parameters lower positive bounded 0 0 data)).trans
      (mul_le_mul_of_nonneg_left (strongToLow_bound parameters lower positive bounded 0 0 data) (norm_nonneg _))

end Grad.AnnularStrongOrbit
