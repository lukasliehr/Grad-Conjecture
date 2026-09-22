import ANK1LiteralMultiplierKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualScalarResidual
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.RawCircularSectors Grad.CartesianScalarElimination
variable {L sigma gamma ell : ℝ}

theorem vectorDivJet_rawVector (mode : ℤ) (field : ClosedJet 2) :
    vectorDivJet (rawVectorJet mode field) = angularClosedJet mode (vectorDivJet field) := by
  change planarCurlJet (valueMapJet quarterValueMap (rawVectorJet mode field)) = _
  rw [← rawVectorJet_quarter, planarCurlJet_rawVector]
  rfl

theorem planarDivJet_rawVector (mode : ℤ) (field : ClosedJet 2) :
    planarDivJet (valueMapJet planarInclusionMap (rawVectorJet mode field)) =
      angularClosedJet mode (planarDivJet (valueMapJet planarInclusionMap field)) := by
  rw [← vectorDivJet_actual, ← vectorDivJet_actual, vectorDivJet_rawVector]

theorem planarDivJet_rawStored (mode : ℤ) (field : ClosedJet 3) :
    planarDivJet (rawStoredJet mode field) = angularClosedJet mode (planarDivJet field) := by
  have actual (stored : ClosedJet 3) : vectorDivJet (valueMapJet planarPartMap stored) = planarDivJet stored :=
    planarCurlJet_quarter_planar stored
  rw [← actual, rawStoredJet_planar, vectorDivJet_rawVector, actual]

/-- The actual three-coordinate divergence includes the original scaled axial
frequency. Raw covariance holds at every cell, including frequency zero. -/
theorem apSmoothDiv_rawStored (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (field : APSmooth L sigma gamma ell 3) :
    apSmoothDiv admissible (apSmoothRawStored L sigma gamma ell mode field) =
      apSmoothAngularMode L sigma gamma ell 1 mode (apSmoothDiv admissible field) := by
  apply apSmoothJet_ext admissible
  intro cell
  have geometric (jet : ClosedJet 3) :
      planarDivJet (rawStoredJet mode jet) + seedScaledFrequency L ell cell •
        valueMapJet toroidalPartMap (rawStoredJet mode jet) =
      angularClosedJet mode (planarDivJet jet + seedScaledFrequency L ell cell • valueMapJet toroidalPartMap jet) := by
    rw [planarDivJet_rawStored, rawStoredJet_scalar, angularClosedJet_add, angularClosedJet_smul]
  have left := (apSmoothDiv_jet admissible (apSmoothRawStored L sigma gamma ell mode field) cell).trans
    (congrArg (fun jet : ClosedJet 3 => planarDivJet jet + seedScaledFrequency L ell cell • valueMapJet toroidalPartMap jet)
      (apSmoothRawStored_jet admissible mode field cell))
  have right := (apSmoothAngularMode_jet admissible mode (apSmoothDiv admissible field) cell).trans
    (congrArg (angularClosedJet mode) (apSmoothDiv_jet admissible field cell))
  exact left.trans ((geometric _).trans right.symm)

/-- Any actual raw-excluded state has raw-excluded full reconstructed divergence. -/
theorem state_divergence_excluded (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell) (excluded : AvoidsExceptionalState state) :
    Grad.ActualNonexceptionalInverse.ScalarAvoidsExceptional admissible
      (apSmoothDiv admissible (compensatedReconstruct admissible state)) := by
  intro cell mode exceptional
  have reconstructed := (rawStateProjector_reconstruct admissible mode state).symm.trans
    ((congrArg (compensatedReconstruct admissible) (excluded mode exceptional)).trans (map_zero _))
  have projected := (apSmoothDiv_rawStored admissible mode (compensatedReconstruct admissible state)).symm.trans
    ((congrArg (apSmoothDiv admissible) reconstructed).trans (map_zero _))
  exact (apSmoothAngularMode_jet admissible mode _ cell).symm.trans
    ((congrArg (apSmoothJet admissible 1 cell) projected).trans (map_zero _))

end Grad.ActualScalarResidual
