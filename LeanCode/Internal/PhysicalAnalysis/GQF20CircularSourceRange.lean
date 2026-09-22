import GQF19SourceMean

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Frame Grad.NonlinearDivision Grad.NonlinearRange

variable {L sigma gamma ell : ℝ}

theorem circularForceInner_jet (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell) (cell : ℤ) :
    apSmoothJet admissible 2 cell (circularForceInner admissible state) =
      closedCircularForce (apSmoothJet admissible 1 cell state.1) (apSmoothJet admissible 3 cell state.2) := by
  have first := (apSmoothValueMap_jet admissible quarterValueMap (apSmoothGradient admissible state.1) cell).trans
    (congrArg (valueMapJet quarterValueMap) (apSmoothGradient_jet admissible state.1 cell))
  have planar := apSmoothValueMap_jet admissible planarPartMap state.2 cell
  have second := (apSmoothRotation_jet admissible (apSmoothPlanar L sigma gamma ell state.2) cell).trans
    (congrArg rotationJet planar)
  have third := (apSmoothValueMap_jet admissible quarterValueMap
    (apSmoothPlanar L sigma gamma ell state.2) cell).trans (congrArg (valueMapJet quarterValueMap) planar)
  exact (map_sub (apSmoothJet admissible 2 cell) _ _).trans
    (congrArg₂ (fun first second : ClosedJet 2 => first - second)
      ((map_smul (apSmoothJet admissible 2 cell) (-2 : ℂ) _).trans
        (congrArg (fun value : ClosedJet 2 => (-2 : ℂ) • value) first))
      ((map_add (apSmoothJet admissible 2 cell) _ _).trans
        (congrArg₂ (fun first second : ClosedJet 2 => first + second) second third)))

theorem smoothCapSource_mem (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell)
    (radial : apSmoothQrad L sigma gamma ell source.1 = source.1)
    (axis : APSmoothAxisValueZero admissible source.1)
    (curl : APSmoothAxisValueZero admissible (apSmoothCurl admissible source.1))
    (determinant : APSmoothMeanZero admissible source.2.1)
    (thirdMean : APSmoothMeanZero admissible source.2.2)
    (thirdFirst : APSmoothAxisFirstJetZero admissible source.2.2) :
    source ∈ smoothCapSourceCore admissible := by
  simp only [smoothCapSourceCore, Submodule.mem_inf, Submodule.mem_comap, LinearMap.mem_ker,
    LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, mem_apSmoothAxisValues, mem_apSmoothMeanFree,
    mem_apSmoothAxisFirsts]
  tauto

theorem circularForce_axis (admissible : Admissible L sigma gamma ell)
    (state : compensatedFlatCore admissible) : APSmoothAxisValueZero admissible (circularForce admissible state.val) := by
  intro cell
  have original := (mem_compensatedFlatCore admissible state.val).mp state.property
  have thetaFlat := apSmoothAxisFirstJetZero_closed admissible state.val.1 original.1.2 cell
  have total := (congrArg ClosedFirstJetZero (compensatedReconstruct_jet admissible state.val cell)).mp
    (apSmoothAxisFirstJetZero_closed admissible (compensatedReconstruct admissible state.val) original.2 cell)
  exact (apSmoothQrad_origin admissible (circularForceInner admissible state.val) cell).trans
    ((congrArg (fun jet : ClosedJet 2 => jet.value closedOrigin)
      (circularForceInner_jet admissible state.val cell)).trans
        (closedCircularForce_origin (seedScaledFrequency L ell cell) _ _ thetaFlat total))

theorem circularForce_curl_axis (admissible : Admissible L sigma gamma ell)
    (state : compensatedFlatCore admissible) :
    APSmoothAxisValueZero admissible (apSmoothCurl admissible (circularForce admissible state.val)) := by
  intro cell
  have original := (mem_compensatedFlatCore admissible state.val).mp state.property
  have thetaFlat := apSmoothAxisFirstJetZero_closed admissible state.val.1 original.1.2 cell
  have total := (congrArg ClosedFirstJetZero (compensatedReconstruct_jet admissible state.val cell)).mp
    (apSmoothAxisFirstJetZero_closed admissible (compensatedReconstruct admissible state.val) original.2 cell)
  have projected := congrArg (apSmoothJet admissible 1 cell)
    (apSmoothCurl_Qrad admissible (circularForceInner admissible state.val))
  have closed := projected.trans ((apSmoothCurl_jet admissible _ cell).trans
    (congrArg planarCurlJet (circularForceInner_jet admissible state.val cell)))
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  exact (congrArg (fun jet : ClosedJet 1 => jet.value closedOrigin 0) closed).trans
    (closedCircularForce_curl_origin (seedScaledFrequency L ell cell) _ _ thetaFlat total)

/-- Literal AM9 source membership follows from the compensated flat jets;
no circular gauge or PDE inverse is an extra premise. -/
theorem circularRows_source_mem (admissible : Admissible L sigma gamma ell)
    (state : compensatedFlatCore admissible) :
    circularRows admissible state.val ∈ smoothCapSourceCore admissible := by
  apply smoothCapSource_mem admissible
  · exact apSmoothQrad_idempotent admissible (circularForceInner admissible state.val)
  · exact circularForce_axis admissible state
  · exact circularForce_curl_axis admissible state
  · have mean := (mem_apSmoothMeanFree admissible _).mpr
      (apSmoothMeanZero_removeMean admissible (apSmoothDiv admissible (compensatedReconstruct admissible state.val)))
    exact (mem_apSmoothMeanFree admissible _).mp ((apSmoothMeanFree admissible).neg_mem mean)
  · exact apSmoothMeanZero_rotation admissible (apSmoothScalar L sigma gamma ell state.val.2)
  · exact apSmoothRotation_preserves_firstJet admissible _ (scalarRemainder_firstJet admissible state)

end Grad.GaugeCoefficients.Physical.Compensated
