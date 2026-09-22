import ANP11LiteralExclusions
import ANS7ExactAngularInverse

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.RawCircularSectors
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.NonlinearRange Grad.ActualCenterVolterra Grad.ActualAngularInverse

theorem rotationJet_angular (dimension : ℕ) (mode : ℤ) (field : ClosedJet dimension) :
    rotationJet (angularClosedJet mode field) = angularClosedJet mode (rotationJet field) :=
  (pureMode_rotation mode _ ((angularClosedJet_projection mode mode field).trans (if_pos rfl))).trans
    (angular_rotationJet_all mode field).symm

theorem rotationJet_rawVector (mode : ℤ) (field : ClosedJet 2) :
    rotationJet (rawVectorJet mode field) = rawVectorJet mode (rotationJet field) := by
  rw [rawVectorJet_eq, rawVectorJet_eq, rotationJet_add, rotationJet_valueMap,
    rotationJet_valueMap, rotationJet_angular, rotationJet_angular]

variable {L sigma gamma ell : ℝ}

theorem apSmoothRotation_angular (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (mode : ℤ) (field : APSmooth L sigma gamma ell dimension) :
    apSmoothRotation admissible dimension (apSmoothAngularMode L sigma gamma ell dimension mode field) =
      apSmoothAngularMode L sigma gamma ell dimension mode (apSmoothRotation admissible dimension field) := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothRotation_jet admissible _ cell).trans
    ((congrArg rotationJet (apSmoothAngularMode_jet admissible mode field cell)).trans
      ((rotationJet_angular dimension mode _).trans
        ((congrArg (angularClosedJet mode) (apSmoothRotation_jet admissible field cell).symm).trans
          (apSmoothAngularMode_jet admissible mode _ cell).symm)))

theorem apSmoothRotation_rawVector (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (field : APSmooth L sigma gamma ell 2) :
    apSmoothRotation admissible 2 (apSmoothRawVector L sigma gamma ell mode field) =
      apSmoothRawVector L sigma gamma ell mode (apSmoothRotation admissible 2 field) := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothRotation_jet admissible _ cell).trans
    ((congrArg rotationJet (apSmoothRawVector_jet admissible mode field cell)).trans
      ((rotationJet_rawVector mode _).trans
        ((congrArg (rawVectorJet mode) (apSmoothRotation_jet admissible field cell).symm).trans
          (apSmoothRawVector_jet admissible mode _ cell).symm)))

end Grad.RawCircularSectors
