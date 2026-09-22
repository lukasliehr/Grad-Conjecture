import AKY6ActualNormalizedRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.CartesianUncompressed
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

variable {L sigma gamma ell : ℝ}

theorem circularThird_normalized (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell)
    (mean : APSmoothMeanZero admissible state.1) :
    circularThird admissible state = apSmoothRotation admissible 1
      (apSmoothScalar L sigma gamma ell (actualErQuotient admissible state) -
        apSmoothAxial L sigma gamma ell 1 state.1) := by
  have representation := (compensatedBackward_reconstruct admissible state mean).symm
  have scalar := congrArg (apSmoothScalar L sigma gamma ell) representation
  have expanded := (apSmoothScalar L sigma gamma ell).map_add
    (apSmoothCovariant admissible state.1) (apSmoothCircle L sigma gamma ell state.2)
  have parts := congrArg (fun value : APSmooth L sigma gamma ell 1 =>
    value + apSmoothScalar L sigma gamma ell (apSmoothCircle L sigma gamma ell state.2))
      (apScalar_covariant admissible state.1)
  have scalarRepresentation := scalar.trans (expanded.trans parts)
  have recovered := (congrArg (fun value : APSmooth L sigma gamma ell 1 =>
    value - apSmoothAxial L sigma gamma ell 1 state.1) scalarRepresentation).trans
      (add_sub_cancel_left _ _)
  exact (congrArg (fun row : SmoothCapSource L sigma gamma ell => row.2.2)
    (circularRows_backward admissible state)).symm.trans
      (congrArg (apSmoothRotation admissible 1) recovered.symm)

theorem actualThird_normalized (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (state : CompensatedData L sigma gamma ell)
    (mean : APSmoothMeanZero admissible state.1) :
    actualThird admissible data coherent state +
      actualErThirdCorrection admissible data coherent (compensatedReconstruct admissible state) =
        apSmoothRotation admissible 1
          (apSmoothScalar L sigma gamma ell (actualErQuotient admissible state) -
            apSmoothAxial L sigma gamma ell 1 state.1) := by
  exact (sub_add_cancel (circularThird admissible state)
    (actualErThirdCorrection admissible data coherent (compensatedReconstruct admissible state))).trans
      (circularThird_normalized admissible state mean)

theorem projectedDiv_quotient (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) :
    apSmoothRemoveMean L sigma gamma ell 1
      (apSmoothDiv admissible (apSmoothCircle L sigma gamma ell field)) =
        apSmoothRemoveMean L sigma gamma ell 1 (apSmoothDiv admissible field) := by
  let projected := (apSmoothRemoveMean L sigma gamma ell 1).comp (apSmoothDiv admissible)
  exact (projected.map_sub field (apSmoothComplement L sigma gamma ell field)).trans
    ((congrArg (fun value : APSmooth L sigma gamma ell 1 => projected field - value)
      (apSmoothRemoveMean_div_complement admissible field)).trans (sub_zero _))

/-- The determinant row retains the complete actual flux-deviation action.
Only its circular complement is cancelled, by the proved divergence identity. -/
theorem actualDeterminant_normalized (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (state : CompensatedData L sigma gamma ell) :
    actualDeterminant admissible data coherent state =
      apSmoothRemoveMean L sigma gamma ell 1 (apSmoothDiv admissible
        (-actualErQuotient admissible state +
          actualErFlux admissible data coherent (compensatedReconstruct admissible state))) := by
  let projected := (apSmoothRemoveMean L sigma gamma ell 1).comp (apSmoothDiv admissible)
  have left := (projected.map_add (-(compensatedReconstruct admissible state))
    (actualErFlux admissible data coherent (compensatedReconstruct admissible state))).trans
      (congrArg (fun value => value + projected
        (actualErFlux admissible data coherent (compensatedReconstruct admissible state)))
          (projected.map_neg (compensatedReconstruct admissible state)))
  have right := (projected.map_add (-actualErQuotient admissible state)
    (actualErFlux admissible data coherent (compensatedReconstruct admissible state))).trans
      (congrArg (fun value => value + projected
        (actualErFlux admissible data coherent (compensatedReconstruct admissible state)))
          (projected.map_neg (actualErQuotient admissible state)))
  have middle := congrArg (fun value : APSmooth L sigma gamma ell 1 => -value + projected
    (actualErFlux admissible data coherent (compensatedReconstruct admissible state)))
      (projectedDiv_quotient admissible (compensatedReconstruct admissible state)).symm
  exact left.trans (middle.trans right.symm)

/-- The multiplier inputs in the ER rows are exactly Qa of the fixed quotient
whenever the original physical current gauge vanishes. -/
theorem actualErRows_use_current_projection
    (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (laws : ∀ grade, ActualProjectionLaws admissible data.gaugeDeviation grade)
    (state : CompensatedData L sigma gamma ell)
    (currentGauge : apSmoothGauge admissible data.gaugeDeviation coherent.2.2.2.1
      (compensatedReconstruct admissible state) = 0) :
    apSmoothCurrent admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent
      (actualErQuotient admissible state) = compensatedReconstruct admissible state :=
  actualCurrent_quotient_recover admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent laws
    (compensatedReconstruct admissible state) currentGauge

end Grad.CartesianUncompressed
