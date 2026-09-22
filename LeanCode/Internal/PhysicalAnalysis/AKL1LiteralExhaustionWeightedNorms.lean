import AKE4SolvedFiveBlockInverse
import AJF51SameOriginalSharedInverseTame

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularExhaustionEstimate
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularForwardDatum Grad.AnnularForwardTraces Grad.AnnularStrongOrbit
open Grad.AnnularHighGenerators Grad.AnnularCrossOrbit Grad.AnnularCoupledInverse
open Grad.AnnularCurrentSource Grad.SourceCollarDivision Grad.AnnularSourceGraph
open Grad.AnnularHighTilt Grad.AnnularLowEnergy Grad.SourceCollarFullSource
attribute [local instance] Grad.AnnularStrongOrbit.knownAmbientNormed Grad.AnnularStrongOrbit.knownAmbientSeminormed Grad.AnnularStrongOrbit.knownAmbientRealNormed Grad.AnnularStrongOrbit.knownAmbientRealModule
  Grad.AnnularStrongOrbit.strongCarrierNormed Grad.AnnularStrongOrbit.strongCarrierSeminormed Grad.AnnularStrongOrbit.strongCarrierRealNormed Grad.AnnularStrongOrbit.strongCarrierRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace
  Grad.AnnularCrossOrbit.coupledNormed Grad.AnnularCrossOrbit.coupledSeminormed
  Grad.AnnularCrossOrbit.coupledComplexNormed Grad.AnnularCrossOrbit.coupledComplexModule
  Grad.AnnularCrossOrbit.coupledRealNormed Grad.AnnularCrossOrbit.coupledRealModule
  Grad.AnnularCrossOrbit.coupledOperatorRealNormed Grad.AnnularCrossOrbit.coupledOperatorRealModule



private theorem expandFourInEight {total bulk first second third fourth g rg graph0 graph2 outer high low : ℝ}
    (all : total = bulk + g + rg + graph0 + graph2 + outer + high + low)
    (four : bulk = first + second + third + fourth) :
    total = first + second + third + fourth + g + rg + graph0 + graph2 + outer + high + low := by
  linarith only [all, four]

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length)

/-- The original independently prescribed datum in its exact BF weighted coordinates. -/
def originalWeightedDatum (data : OriginalStrongCarrier parameters lower 0 0) :
    StrongDataCarrier parameters lower positive bounded 0 0 :=
  originalStrongWeightEquivalence parameters lower length positive bounded lengthPositive 0 0 data

def originalWeightedDatumNorm (data : OriginalStrongCarrier parameters lower 0 0) : ℝ :=
  ‖originalWeightedDatum parameters lower length positive bounded lengthPositive data‖

theorem originalWeightedDatum_explicit (data : OriginalStrongCarrier parameters lower 0 0) :
    originalWeightedDatum parameters lower length positive bounded lengthPositive data =
      originalToStrong parameters lower length positive bounded lengthPositive 0 0 data :=
  originalStrongWeightEquivalence_eq_reconstruction parameters lower length positive bounded lengthPositive 0 0 data

/-- Six actual tilted bulk rows, the two original source graphs, and all three
original boundary coordinates. No small-radius comparison constant enters. -/
theorem originalWeightedDatumNorm_sq (data : OriginalStrongCarrier parameters lower 0 0) :
    originalWeightedDatumNorm parameters lower length positive bounded lengthPositive data ^ 2 =
      ‖divisionHighWeight lower positive bounded
        (unweightedSourceF0Bulk parameters lower data.val.ofLp.1.ofLp.1.ofLp.1)‖ ^ 2 +
      ‖divisionHighWeight lower positive bounded
        (unweightedSourceRF0Bulk parameters lower data.val.ofLp.1.ofLp.1.ofLp.1)‖ ^ 2 +
      ‖divisionHighWeight lower positive bounded
        (unweightedSourceF2Bulk parameters lower data.val.ofLp.1.ofLp.1.ofLp.2)‖ ^ 2 +
      ‖divisionHighWeight lower positive bounded data.val.ofLp.1.ofLp.2.ofLp.1‖ ^ 2 +
      ‖divisionHighWeight lower positive bounded
        (originalAngularDecode lower data.val.ofLp.1.ofLp.2.ofLp.2)‖ ^ 2 +
      ‖divisionHighWeight lower positive bounded
        (sourceAngularBulk lower data.val.ofLp.1.ofLp.2.ofLp.2)‖ ^ 2 +
      ‖data.val.ofLp.1.ofLp.1.ofLp.1‖ ^ 2 + ‖data.val.ofLp.1.ofLp.1.ofLp.2‖ ^ 2 +
      ‖data.val.ofLp.2.ofLp.1‖ ^ 2 +
      ‖lower ^ (-9 / 4 : ℝ) • data.val.ofLp.2.ofLp.2.ofLp.1‖ ^ 2 +
      ‖originalLowIncomingWeightMap parameters lower length positive bounded lengthPositive
        data.val.ofLp.2.ofLp.2.ofLp.2‖ ^ 2 := by
  have normSame := congrArg
    (fun field : StrongDataCarrier parameters lower positive bounded 0 0 => ‖field‖ ^ 2)
    (originalWeightedDatum_explicit parameters lower length positive bounded lengthPositive data)
  apply normSame.trans
  have total := StrongDataCarrier.norm_sq parameters lower positive bounded 0 0
    (originalToStrong parameters lower length positive bounded lengthPositive 0 0 data)
  have bulk := highKnownSourceBulk_norm_sq lower
    (originalToStrong parameters lower length positive bounded lengthPositive 0 0 data).val.ofLp.1.ofLp.1.ofLp.1
  exact expandFourInEight total bulk

/-- Exact retained weighting of the same original candidate. -/
def originalWeightedRetained (field : OriginalCoupledSpace lower length positive) :
    CoupledSpace lower length positive lengthPositive :=
  originalCoupledEquivalence parameters lower length positive bounded lengthPositive field

def originalWeightedRetainedNorm (field : OriginalCoupledSpace lower length positive) : ℝ :=
  ‖originalWeightedRetained parameters lower length positive bounded lengthPositive field‖

theorem originalWeightedRetainedNorm_sq (field : OriginalCoupledSpace lower length positive) :
    let weighted := originalWeightedRetained parameters lower length positive bounded lengthPositive field
    originalWeightedRetainedNorm parameters lower length positive bounded lengthPositive field ^ 2 =
      ‖weighted.ofLp.1.ofLp.1‖ ^ 2 +
      (‖weighted.ofLp.1.ofLp.2.val 0‖ ^ 2 + ‖weighted.ofLp.1.ofLp.2.val 1‖ ^ 2) +
      (‖weighted.ofLp.2.val 0‖ ^ 2 + ‖weighted.ofLp.2.val 1‖ ^ 2) :=
  coupledSpace_original_graph_norm_sq lower length positive lengthPositive _

end Grad.AnnularExhaustionEstimate
