import AKY7ActualScalarAndFluxRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.CartesianUncompressed
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Frame Grad.RawCircularSectors Grad.NonlinearRange
open Grad.CartesianScalarElimination

variable {L sigma gamma ell : ℝ}

theorem planarDivJet_components (field : ClosedJet 3) :
    planarDivJet field = vectorDivJet (valueMapJet planarPartMap field) :=
  (planarCurlJet_quarter_planar field).symm

theorem actualForce_fullCell (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (state : CompensatedData L sigma gamma ell)
    (mean : APSmoothMeanZero admissible state.1) (cell : ℤ) :
    apSmoothJet admissible 2 cell (actualForce admissible data coherent state) -
      apSmoothJet admissible 2 cell (actualErForceCorrection admissible data coherent
        (compensatedReconstruct admissible state)) =
          gradientJet (rotationJet (apSmoothJet admissible 1 cell state.1)) -
            (rotationJet (apSmoothJet admissible 2 cell
              (apSmoothPlanar L sigma gamma ell (actualErQuotient admissible state))) +
                valueMapJet quarterValueMap (apSmoothJet admissible 2 cell
                  (apSmoothPlanar L sigma gamma ell (actualErQuotient admissible state)))) := by
  have row := congrArg (apSmoothJet admissible 2 cell)
    (actualForce_normalized admissible data coherent state mean)
  simp only [map_sub, map_add, apSmoothGradient_jet, apSmoothRotation_jet] at row
  have quarter := apSmoothValueMap_jet admissible quarterValueMap
    (apSmoothPlanar L sigma gamma ell (actualErQuotient admissible state)) cell
  exact row.trans (congrArg (fun value : ClosedJet 2 =>
    gradientJet (rotationJet (apSmoothJet admissible 1 cell state.1)) -
      (rotationJet (apSmoothJet admissible 2 cell
        (apSmoothPlanar L sigma gamma ell (actualErQuotient admissible state))) + value)) quarter)

theorem actualThird_fullCell (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (state : CompensatedData L sigma gamma ell)
    (mean : APSmoothMeanZero admissible state.1) (cell : ℤ) :
    apSmoothJet admissible 1 cell (actualThird admissible data coherent state) +
      apSmoothJet admissible 1 cell (actualErThirdCorrection admissible data coherent
        (compensatedReconstruct admissible state)) =
          rotationJet (apSmoothJet admissible 1 cell
            (apSmoothScalar L sigma gamma ell (actualErQuotient admissible state)) -
              seedScaledFrequency L ell cell • apSmoothJet admissible 1 cell state.1) := by
  have row := congrArg (apSmoothJet admissible 1 cell)
    (actualThird_normalized admissible data coherent state mean)
  simpa only [map_add, apSmoothRotation_jet, map_sub, apSmoothAxial_jet, scalarRotation_sub] using row

theorem actualQuotient_fullCell_gauges (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell) (cell : ℤ) :
    tangentialJet (apSmoothJet admissible 2 cell
      (apSmoothPlanar L sigma gamma ell (actualErQuotient admissible state))) = 0 ∧
    angularClosedJet 0 (apSmoothJet admissible 1 cell
      (apSmoothScalar L sigma gamma ell (actualErQuotient admissible state))) = 0 := by
  have gauges := actualQuotient_componentGauges admissible (compensatedReconstruct admissible state)
  constructor
  · exact (apSmoothTangential_jet admissible _ cell).symm.trans
      ((congrArg (apSmoothJet admissible 2 cell) gauges.1).trans (map_zero _))
  · exact (apSmoothAngularMean_jet admissible _ cell).symm.trans
      ((congrArg (apSmoothJet admissible 1 cell) gauges.2).trans (map_zero _))

end Grad.CartesianUncompressed
