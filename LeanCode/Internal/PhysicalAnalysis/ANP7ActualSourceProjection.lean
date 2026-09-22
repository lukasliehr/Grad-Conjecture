import ANP6ClosedGaugePreservation
import ANM2ActualMeanSource

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.RawCircularSectors
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.ActualMeanInverse
variable {L sigma gamma ell : ℝ}

/-- The literal raw-sector projector on the existing full-cell source carrier. -/
def rawSourceProjector (L sigma gamma ell : ℝ) (mode : ℤ) :
    SmoothCapSource L sigma gamma ell →ₗ[ℂ] SmoothCapSource L sigma gamma ell :=
  ((apSmoothRawVector L sigma gamma ell mode).comp (LinearMap.fst ℂ _ _)).prod
    (((apSmoothAngularMode L sigma gamma ell 1 mode).comp ((LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _))).prod
      ((apSmoothAngularMode L sigma gamma ell 1 mode).comp ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _))))

theorem apSmoothRawVector_quarter (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (field : APSmooth L sigma gamma ell 2) :
    apSmoothRawVector L sigma gamma ell mode (apSmoothQuarter L sigma gamma ell field) =
      apSmoothQuarter L sigma gamma ell (apSmoothRawVector L sigma gamma ell mode field) := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothRawVector_jet admissible mode _ cell).trans
    ((congrArg (rawVectorJet mode) (apSmoothValueMap_jet admissible quarterValueMap field cell)).trans
      ((rawVectorJet_quarter mode _).trans
        ((congrArg (valueMapJet quarterValueMap) (apSmoothRawVector_jet admissible mode field cell).symm).trans
          (apSmoothValueMap_jet admissible quarterValueMap _ cell).symm)))

theorem apSmoothRawVector_tangential (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (field : APSmooth L sigma gamma ell 2) :
    apSmoothRawVector L sigma gamma ell mode (apSmoothTangential L sigma gamma ell field) =
      apSmoothTangential L sigma gamma ell (apSmoothRawVector L sigma gamma ell mode field) := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothRawVector_jet admissible mode _ cell).trans
    ((congrArg (rawVectorJet mode) (apSmoothTangential_jet admissible field cell)).trans
      ((rawVectorJet_tangential mode _).trans
        ((congrArg tangentialJet (apSmoothRawVector_jet admissible mode field cell).symm).trans
          (apSmoothTangential_jet admissible _ cell).symm)))

private theorem commute_radial {E : Type*} [AddCommGroup E] [Module ℂ E]
    (projector quarter tangent : E →ₗ[ℂ] E)
    (turns : ∀ field, projector (quarter field) = quarter (projector field))
    (tangents : ∀ field, projector (tangent field) = tangent (projector field)) (field : E) :
    projector (field + quarter (tangent (quarter field))) =
      projector field + quarter (tangent (quarter (projector field))) := by
  rw [map_add, turns, tangents, turns]

theorem apSmoothRawVector_Qrad (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (field : APSmooth L sigma gamma ell 2) :
    apSmoothRawVector L sigma gamma ell mode (apSmoothQrad L sigma gamma ell field) =
      apSmoothQrad L sigma gamma ell (apSmoothRawVector L sigma gamma ell mode field) :=
  commute_radial (apSmoothRawVector L sigma gamma ell mode) (apSmoothQuarter L sigma gamma ell)
    (apSmoothTangential L sigma gamma ell) (apSmoothRawVector_quarter admissible mode)
    (apSmoothRawVector_tangential admissible mode) field

theorem apSmoothCurl_rawVector (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (field : APSmooth L sigma gamma ell 2) :
    apSmoothCurl admissible (apSmoothRawVector L sigma gamma ell mode field) =
      apSmoothAngularMode L sigma gamma ell 1 mode (apSmoothCurl admissible field) := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothCurl_jet admissible _ cell).trans
    ((congrArg planarCurlJet (apSmoothRawVector_jet admissible mode field cell)).trans
      ((planarCurlJet_rawVector mode _).trans
        ((congrArg (angularClosedJet mode) (apSmoothCurl_jet admissible field cell).symm).trans
          (apSmoothAngularMode_jet admissible mode _ cell).symm)))

theorem apSmoothAngularMode_axis_zero (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (mode : ℤ) (field : APSmooth L sigma gamma ell dimension)
    (zero : APSmoothAxisValueZero admissible field) :
    APSmoothAxisValueZero admissible (apSmoothAngularMode L sigma gamma ell dimension mode field) := by
  intro cell
  exact (congrArg (fun jet : ClosedJet dimension => jet.value Grad.NonlinearDivision.closedOrigin)
    (apSmoothAngularMode_jet admissible mode field cell)).trans (angular_axis_value_zero mode _ (zero cell))

theorem apSmoothAngularMode_firstJet_zero (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (mode : ℤ) (field : APSmooth L sigma gamma ell dimension)
    (zero : APSmoothAxisFirstJetZero admissible field) :
    APSmoothAxisFirstJetZero admissible (apSmoothAngularMode L sigma gamma ell dimension mode field) := by
  apply apSmoothAxisFirstJetZero_of_closed
  intro cell
  exact (congrArg ClosedFirstJetZero (apSmoothAngularMode_jet admissible mode field cell)).mpr
    (closedFirstJetZero_angular _ (apSmoothAxisFirstJetZero_closed admissible field zero cell) mode)

theorem apSmoothAngularMode_mean_zero (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (field : APSmooth L sigma gamma ell 1) (zero : APSmoothMeanZero admissible field) :
    APSmoothMeanZero admissible (apSmoothAngularMode L sigma gamma ell 1 mode field) := by
  intro cell
  have law := (congrArg (angularClosedJet 0) (apSmoothAngularMode_jet admissible mode field cell)).trans
    (angularClosedJet_projection 0 mode _)
  by_cases same : 0 = mode
  · exact law.trans ((if_pos same).trans (zero cell))
  · exact law.trans (if_neg same)

theorem mem_actualSource_iff (admissible : Admissible L sigma gamma ell) (source : SmoothCapSource L sigma gamma ell) :
    source ∈ smoothCapSourceCore admissible ↔
      (apSmoothQrad L sigma gamma ell source.1 = source.1 ∧ APSmoothAxisValueZero admissible source.1 ∧
        APSmoothAxisValueZero admissible (apSmoothCurl admissible source.1)) ∧
      APSmoothMeanZero admissible source.2.1 ∧ APSmoothMeanZero admissible source.2.2 ∧
        APSmoothAxisFirstJetZero admissible source.2.2 := by
  simp only [smoothCapSourceCore, Submodule.mem_inf, Submodule.mem_comap, LinearMap.mem_ker,
    LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, mem_apSmoothAxisValues, mem_apSmoothMeanFree,
    mem_apSmoothAxisFirsts, and_assoc]

/-- AM9 compatibility is preserved literally, including force and curl axis
values and the high source's first jet, at every original analytic cell. -/
theorem rawSourceProjector_preserves (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible) :
    rawSourceProjector L sigma gamma ell mode source ∈ smoothCapSourceCore admissible := by
  have original := actualSource_conditions admissible source compatible
  apply (mem_actualSource_iff admissible _).mpr
  refine ⟨⟨?_, ?_, ?_⟩, apSmoothAngularMode_mean_zero admissible mode _ original.2.1,
    apSmoothAngularMode_mean_zero admissible mode _ original.2.2.1,
    apSmoothAngularMode_firstJet_zero admissible mode _ original.2.2.2⟩
  · exact (apSmoothRawVector_Qrad admissible mode source.1).symm.trans
      (congrArg (apSmoothRawVector L sigma gamma ell mode) original.1.1)
  · intro cell
    exact (congrArg (fun jet : ClosedJet 2 => jet.value Grad.NonlinearDivision.closedOrigin)
      (apSmoothRawVector_jet admissible mode source.1 cell)).trans
        (rawVectorJet_axis_value_zero mode _ (original.1.2.1 cell))
  · exact (congrArg (APSmoothAxisValueZero admissible) (apSmoothCurl_rawVector admissible mode source.1)).mpr
      (apSmoothAngularMode_axis_zero admissible mode _ original.1.2.2)

theorem rawSourceProjector_sector (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (source : SmoothCapSource L sigma gamma ell) :
    IsRawSourceSector admissible mode (rawSourceProjector L sigma gamma ell mode source) := by
  refine ⟨?_, ?_, ?_⟩
  · intro cell
    have law := apSmoothRawVector_jet admissible mode source.1 cell
    exact (congrArg (fun jet : ClosedJet 2 => rawVectorJet mode jet = jet) law).mpr
      ((rawVectorJet_projection mode mode _).trans (if_pos rfl))
  · intro cell
    have law := apSmoothAngularMode_jet admissible mode source.2.1 cell
    exact (congrArg (fun jet : ClosedJet 1 => angularClosedJet mode jet = jet) law).mpr
      ((angularClosedJet_projection mode mode _).trans (if_pos rfl))
  · intro cell
    have law := apSmoothAngularMode_jet admissible mode source.2.2 cell
    exact (congrArg (fun jet : ClosedJet 1 => angularClosedJet mode jet = jet) law).mpr
      ((angularClosedJet_projection mode mode _).trans (if_pos rfl))

end Grad.RawCircularSectors
