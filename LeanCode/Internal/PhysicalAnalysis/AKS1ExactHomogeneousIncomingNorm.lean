import AKP12FullOriginalFamilyVanishingIncoming
import AKL2SameOriginalUniformRetainedEstimate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.AnnularWeightedUniqueness
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularReconstruction
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularForwardDatum Grad.AnnularForwardTraces Grad.AnnularStrongOrbit
open Grad.AnnularCoupledInverse Grad.AnnularRestriction Grad.AnnularExhaustionEstimate
open Grad.AnnularIncomingIntegrability Grad.SourceCollarDivision Grad.AnnularSourceGraph
open Grad.AnnularCurrentSource Grad.AnnularVariational Grad.AnnularLowEnergy Grad.AnnularTiltedReference
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule
  Grad.AnnularStrongOrbit.knownAmbientNormed Grad.AnnularStrongOrbit.knownAmbientSeminormed
  Grad.AnnularStrongOrbit.knownAmbientRealNormed Grad.AnnularStrongOrbit.knownAmbientRealModule
  Grad.AnnularStrongOrbit.strongCarrierNormed Grad.AnnularStrongOrbit.strongCarrierSeminormed
  Grad.AnnularStrongOrbit.strongCarrierRealNormed Grad.AnnularStrongOrbit.strongCarrierRealModule

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower length positive)
    (boundary : originalBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state
      (candidate,data.val.ofLp.1.ofLp.1) = data.val.ofLp.2)
include boundary

theorem actualHighIncoming_weight :
    lower ^ (-9 / 4 : ℝ) • data.val.ofLp.2.ofLp.2.ofLp.1 =
      annularEnergyTrace lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
        (bEnergyDecode lower length positive
          (originalWeightedRetained parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate).ofLp.1.ofLp.1) := by
  have high := congrArg (fun item : OriginalBoundaryCoordinates parameters => item.ofLp.2.ofLp.1) boundary
  change lower ^ (9 / 4 : ℝ) • annularEnergyTrace lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
    (bEnergyDecode lower length positive
      (originalWeightedRetained parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate).ofLp.1.ofLp.1) = _ at high
  rw [← high, smul_smul, ← Real.rpow_add positive]
  norm_num

theorem actualLowIncoming_weight :
    originalLowIncomingWeightMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
      data.val.ofLp.2.ofLp.2.ofLp.2 =
      lowIncomingTrace lower length positive (lowerHalf.trans_lt (by norm_num))
        (originalWeightedRetained parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate).ofLp.2 := by
  have low := congrArg (fun item : OriginalBoundaryCoordinates parameters => item.ofLp.2.ofLp.2) boundary
  change originalLowIncomingUnweightMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
    (lowIncomingTrace lower length positive (lowerHalf.trans_lt (by norm_num))
      (originalWeightedRetained parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate).ofLp.2) = _ at low
  rw [← low]
  exact (originalLowIncomingWeightMap_inverse parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive _).1

/-- For a homogeneous full source and physical outer datum, the exact BF
weighted datum norm is precisely the solution's own full incoming norm. -/
theorem originalHomogeneousDatumNorm_eq_incoming
    (sources : data.val.ofLp.1 = 0) (outer : data.val.ofLp.2.ofLp.1 = 0) :
    originalWeightedDatumNorm parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive data =
      ‖coupledIncomingTrace lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
        (originalWeightedRetained parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate)‖ := by
  have square := originalWeightedDatumNorm_sq parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive data
  have sourceSquare := congrArg (fun source : ForwardSourceBlocks parameters lower =>
      ‖divisionHighWeight lower positive (lowerHalf.trans (by norm_num))
        (unweightedSourceF0Bulk parameters lower source.ofLp.1.ofLp.1)‖ ^ 2 +
      ‖divisionHighWeight lower positive (lowerHalf.trans (by norm_num))
        (unweightedSourceRF0Bulk parameters lower source.ofLp.1.ofLp.1)‖ ^ 2 +
      ‖divisionHighWeight lower positive (lowerHalf.trans (by norm_num))
        (unweightedSourceF2Bulk parameters lower source.ofLp.1.ofLp.2)‖ ^ 2 +
      ‖divisionHighWeight lower positive (lowerHalf.trans (by norm_num)) source.ofLp.2.ofLp.1‖ ^ 2 +
      ‖divisionHighWeight lower positive (lowerHalf.trans (by norm_num))
        (originalAngularDecode lower source.ofLp.2.ofLp.2)‖ ^ 2 +
      ‖divisionHighWeight lower positive (lowerHalf.trans (by norm_num))
        (sourceAngularBulk lower source.ofLp.2.ofLp.2)‖ ^ 2 +
      ‖source.ofLp.1.ofLp.1‖ ^ 2 + ‖source.ofLp.1.ofLp.2‖ ^ 2) sources
  simp only [WithLp.ofLp_zero, Prod.fst_zero, Prod.snd_zero, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at sourceSquare
  have outerSquare := congrArg (fun value => ‖value‖ ^ 2) outer
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0)] at outerSquare
  have highSquare := congrArg (fun value => ‖value‖ ^ 2)
    (actualHighIncoming_weight parameters length compact lower positive lowerHalf lengthPositive state data candidate boundary)
  have lowSquare := congrArg (fun value => ‖value‖ ^ 2)
    (actualLowIncoming_weight parameters length compact lower positive lowerHalf lengthPositive state data candidate boundary)
  have incoming := WithLp.prod_norm_sq_eq_of_L2
    (coupledIncomingTrace lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
      (originalWeightedRetained parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate))
  change ‖coupledIncomingTrace lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
      (originalWeightedRetained parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate)‖ ^ 2 =
    ‖annularEnergyTrace lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (bEnergyDecode lower length positive
        (originalWeightedRetained parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate).ofLp.1.ofLp.1)‖ ^ 2 +
    ‖lowIncomingTrace lower length positive (lowerHalf.trans_lt (by norm_num))
      (originalWeightedRetained parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate).ofLp.2‖ ^ 2 at incoming
  have positiveDatum : 0 ≤ originalWeightedDatumNorm parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive data := norm_nonneg _
  nlinarith only [square, sourceSquare, outerSquare, highSquare, lowSquare, incoming, positiveDatum, norm_nonneg (coupledIncomingTrace lower length positive
    (lowerHalf.trans_lt (by norm_num)) lengthPositive
      (originalWeightedRetained parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate))]

end Grad.AnnularWeightedUniqueness
