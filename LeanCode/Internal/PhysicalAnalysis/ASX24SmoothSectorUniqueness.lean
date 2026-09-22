import ASX23ActualExceptionalRows

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.ActualCenterVolterra
open Grad.NonlinearRange Grad.NonlinearQuotientBounds Grad.RawCircularSectors Grad.FlatSourceProjection
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.RadialLedger
variable {L sigma gamma ell : ℝ}

theorem smoothSecondMode_zero (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (field : APSmooth L sigma gamma ell 1)
    (pure : HasSmoothMode admissible (2 * sign) field)
    (derivative : smoothSignedDerivative admissible 1 sign field = 0) : field = 0 := by
  apply apSmoothJet_ext admissible
  intro cell
  have differential := (smoothSignedDerivative_jet admissible sign field cell).symm.trans
    ((congrArg (apSmoothJet admissible 1 cell) derivative).trans (map_zero _))
  have zeroPure : angularClosedJet (2 * sign) (0 : ClosedJet 1) = 0 := (angularClosedJetLinear 1 (2 * sign)).map_zero
  exact (regularSecondMode_unique sign signed (apSmoothJet admissible 1 cell field) 0 (pure cell) zeroPure
    (differential.trans (signedLowering_zero 1 sign).symm)).trans (map_zero (apSmoothJet admissible 1 cell)).symm

theorem smoothPinnedFirstMode_zero (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (field : APSmooth L sigma gamma ell 1)
    (pure : HasSmoothMode admissible sign field) (pinned : APSmoothAxisFirstJetZero admissible field)
    (derivative : smoothSignedDerivative admissible 1 (-sign) field = 0) : field = 0 := by
  apply apSmoothJet_ext admissible
  intro cell
  have differential := (smoothSignedDerivative_jet admissible (-sign) field cell).symm.trans
    ((congrArg (apSmoothJet admissible 1 cell) derivative).trans (map_zero _))
  have zeroPure : angularClosedJet sign (0 : ClosedJet 1) = 0 := (angularClosedJetLinear 1 sign).map_zero
  have zeroPinned : CenterPinned (0 : ClosedJet 1) := by
    refine ⟨rfl, ?_⟩
    intro direction
    rw [centerPartial_zero]
    rfl
  exact (pinnedSpin_unique sign signed (apSmoothJet admissible 1 cell field) 0 (pure cell) zeroPure
    ((smoothPinned_iff admissible field).mp pinned cell) zeroPinned
    (differential.trans (signedLowering_zero 1 (-sign)).symm)).trans (map_zero (apSmoothJet admissible 1 cell)).symm

theorem rawState_smoothSpin (admissible : Admissible L sigma gamma ell) (mode sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (state : CompensatedData L sigma gamma ell)
    (raw : IsRawStateSector admissible mode state) :
    HasSmoothMode admissible (mode + sign) (smoothSpin L sigma gamma ell sign (apSmoothPlanar L sigma gamma ell state.2)) := by
  intro cell
  rw [smoothSpin_jet]
  exact rawVectorSector_spin sign signed mode _ (raw.2.1 cell)

theorem rawState_divergenceMode (admissible : Admissible L sigma gamma ell) (mode sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (state : CompensatedData L sigma gamma ell)
    (raw : IsRawStateSector admissible mode state) :
    HasSmoothMode admissible mode (apSmoothDiv admissible state.2) := by
  have first : HasSmoothMode admissible mode (smoothSignedDerivative admissible 1 sign
      (smoothSpin L sigma gamma ell sign (apSmoothPlanar L sigma gamma ell state.2))) := by
    simpa only [add_sub_cancel_right] using smoothMode_signedDerivative admissible sign signed (mode + sign) _
      (rawState_smoothSpin admissible mode sign signed state raw)
  have second : HasSmoothMode admissible mode (smoothSignedDerivative admissible 1 (-sign)
      (smoothSpin L sigma gamma ell (-sign) (apSmoothPlanar L sigma gamma ell state.2))) := by
    simpa only [add_sub_cancel_right] using smoothMode_signedDerivative admissible (-sign) (by omega) (mode + -sign) _
      (rawState_smoothSpin admissible mode (-sign) (by omega) state raw)
  exact (congrArg (HasSmoothMode admissible mode) (smoothDiv_spins admissible sign signed state.2)).mpr
    (smoothMode_add admissible mode _ _
      (smoothMode_smul admissible mode (1 / 2 : ℂ) _ (smoothMode_add admissible mode _ _ first second))
      (smoothMode_axial admissible mode _ raw.2.2))

private theorem fixed_evaluation_sub {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (project : F →ₗ[ℂ] F) (evaluate : E →ₗ[ℂ] F) (first second : E)
    (firstFixed : project (evaluate first) = evaluate first) (secondFixed : project (evaluate second) = evaluate second) :
    project (evaluate (first - second)) = evaluate (first - second) :=
  (congrArg project (evaluate.map_sub first second)).trans
    ((project.map_sub _ _).trans ((congrArg₂ (fun a b : F => a - b) firstFixed secondFixed).trans (evaluate.map_sub first second).symm))

theorem rawState_sub (admissible : Admissible L sigma gamma ell) (mode : ℤ)
    (first second : CompensatedData L sigma gamma ell)
    (firstRaw : IsRawStateSector admissible mode first) (secondRaw : IsRawStateSector admissible mode second) :
    IsRawStateSector admissible mode (first - second) := by
  refine ⟨?_, ?_, ?_⟩
  · exact smoothMode_sub admissible mode first.1 second.1 firstRaw.1 secondRaw.1
  · intro cell
    have law := (apSmoothPlanar L sigma gamma ell).map_sub first.2 second.2
    exact (congrArg (fun field : APSmooth L sigma gamma ell 2 =>
      rawVectorJet mode (apSmoothJet admissible 2 cell field) = apSmoothJet admissible 2 cell field) law).mpr
        (fixed_evaluation_sub (rawVectorJetLinear mode) (apSmoothJet admissible 2 cell)
          (apSmoothPlanar L sigma gamma ell first.2) (apSmoothPlanar L sigma gamma ell second.2)
          (firstRaw.2.1 cell) (secondRaw.2.1 cell))
  · exact (congrArg (HasSmoothMode admissible mode) ((apSmoothScalar L sigma gamma ell).map_sub first.2 second.2)).mpr
      (smoothMode_sub admissible mode _ _ firstRaw.2.2 secondRaw.2.2)

end Grad.ActualExceptionalInverse
