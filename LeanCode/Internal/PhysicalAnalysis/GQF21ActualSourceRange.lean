import GQF20CircularSourceRange

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.NonlinearDivision

variable {L sigma gamma ell : ℝ}

theorem apSmoothQrad_preserves_axis (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) (zero : APSmoothAxisValueZero admissible field) :
    APSmoothAxisValueZero admissible (apSmoothQrad L sigma gamma ell field) :=
  fun cell => (apSmoothQrad_origin admissible field cell).trans (zero cell)

theorem apSmoothCurl_axis_of_firstJet (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) (flat : APSmoothAxisFirstJetZero admissible field) :
    APSmoothAxisValueZero admissible (apSmoothCurl admissible field) := by
  intro cell
  have closed := apSmoothAxisFirstJetZero_closed admissible field flat cell
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  have identity := congrArg (fun jet : ClosedJet 1 => jet.value closedOrigin 0)
    (apSmoothCurl_jet admissible field cell)
  exact identity.trans (by rw [planarCurlJet_value, closed.2 0, closed.2 1]; simp)

theorem sourceAxis_smul (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (scalar : ℂ) (field : APSmooth L sigma gamma ell dimension)
    (zero : APSmoothAxisValueZero admissible field) : APSmoothAxisValueZero admissible (scalar • field) :=
  (mem_apSmoothAxisValues admissible _).mp ((apSmoothAxisValues admissible dimension).smul_mem scalar
    ((mem_apSmoothAxisValues admissible field).mpr zero))

theorem errorRows_source_mem (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (field : APSmooth L sigma gamma ell 3) (flat : APSmoothAxisFirstJetZero admissible field) :
    errorRows admissible data coherent field ∈ smoothCapSourceCore admissible := by
  let force := apSmoothMultiplier admissible data.rotatedPlanarProduct coherent.2.2.2.2.2.2.2.1 field
  let third := apSmoothMultiplier admissible data.rotatedThirdProduct coherent.2.2.2.2.2.2.2.2 field
  have forceFlat := apSmoothMultiplier_preserves_firstJet admissible data.rotatedPlanarProduct
    coherent.2.2.2.2.2.2.2.1 field flat
  have thirdFlat := apSmoothMultiplier_preserves_firstJet admissible data.rotatedThirdProduct
    coherent.2.2.2.2.2.2.2.2 field flat
  apply smoothCapSource_mem admissible
  · exact (map_smul (apSmoothQrad L sigma gamma ell) (2 : ℂ)
      (apSmoothQrad L sigma gamma ell force)).trans
        (congrArg (fun value : APSmooth L sigma gamma ell 2 => (2 : ℂ) • value)
          (apSmoothQrad_idempotent admissible force))
  · exact sourceAxis_smul admissible (2 : ℂ) _ (apSmoothQrad_preserves_axis admissible force forceFlat.1)
  · have curlZero := (congrArg (APSmoothAxisValueZero admissible) (apSmoothCurl_Qrad admissible force)).mpr
      (apSmoothCurl_axis_of_firstJet admissible force forceFlat)
    exact (congrArg (APSmoothAxisValueZero admissible)
      (map_smul (apSmoothCurl admissible) (2 : ℂ) (apSmoothQrad L sigma gamma ell force))).mpr
        (sourceAxis_smul admissible (2 : ℂ) _ curlZero)
  · exact apSmoothMeanZero_removeMean admissible
      (apSmoothDiv admissible (apSmoothMultiplier admissible data.fluxDeviation coherent.2.2.2.2.1 field))
  · exact (mem_apSmoothMeanFree admissible _).mp ((apSmoothMeanFree admissible).smul_mem (-2 : ℂ)
      ((mem_apSmoothMeanFree admissible _).mpr (apSmoothMeanZero_removeMean admissible third)))
  · exact (mem_apSmoothAxisFirsts admissible _).mp ((apSmoothAxisFirsts admissible 1).smul_mem (-2 : ℂ)
      ((mem_apSmoothAxisFirsts admissible _).mpr (apSmoothRemoveMean_preserves_firstJet admissible third thirdFlat)))

theorem submodule_mem_of_difference {E : Type*} [AddCommGroup E] [Module ℂ E]
    (subspace : Submodule ℂ E) (first second difference : E)
    (identity : first - second = difference) (differenceMem : difference ∈ subspace)
    (secondMem : second ∈ subspace) : first ∈ subspace := by
  rw [← identity] at differenceMem
  exact sub_add_cancel first second ▸ subspace.add_mem differenceMem secondMem

/-- The literal current rows satisfy AM9 directly. No additional source
projection or maximal-domain replacement is inserted. -/
theorem actualRows_source_mem (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (state : compensatedFlatCore admissible) :
    actualRows admissible data coherent state.val ∈ smoothCapSourceCore admissible := by
  have flat := ((mem_compensatedFlatCore admissible state.val).mp state.property).2
  have circular := circularRows_source_mem admissible state
  have error := errorRows_source_mem admissible data coherent (compensatedReconstruct admissible state.val) flat
  exact submodule_mem_of_difference (smoothCapSourceCore admissible) _ _ _
    (actualRows_difference admissible data coherent state.val) error circular

theorem actualSmoothForwardComparison (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation) :
    SmoothForwardComparison admissible data coherent smooth :=
  ⟨smoothForwardComparison_difference admissible data coherent smooth,
    fun state => circularRows_source_mem admissible ⟨state.val, state.property.1⟩,
    fun state => actualRows_source_mem admissible data coherent ⟨state.val, state.property.1⟩⟩

end Grad.GaugeCoefficients.Physical.Compensated
