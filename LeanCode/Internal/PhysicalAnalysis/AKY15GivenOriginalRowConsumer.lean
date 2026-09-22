import AKY14OriginalB8ReductionConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.CartesianUncompressed
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

def ErCell.withSources (packet : ErCell) (force : ClosedJet 2) (determinant third : ClosedJet 1) : ErCell :=
  { packet with force := force, determinant := determinant, third := third }

theorem ErCell.withSources_eq (packet : ErCell) (force : ClosedJet 2) (determinant third : ClosedJet 1)
    (forceEq : packet.force = force) (determinantEq : packet.determinant = determinant)
    (thirdEq : packet.third = third) : packet.withSources force determinant third = packet := by
  subst force determinant third
  rfl

/-- Exact source consumer: the given rows are the accepted original physical
actualRows, and are substituted into the same-field ER reduction. No separate
operator, finite-cell projection, or scalar recovery unknown is a premise. -/
theorem givenOriginalRows_cartesianReduction {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (state : CompensatedData L parameters.sigma0 parameters.gamma ell)
    (mean : APSmoothMeanZero admissible state.1)
    (source : SmoothCapSource L parameters.sigma0 parameters.gamma ell)
    (rows : actualRows admissible ledger.val ledger.property.1 state = source)
    (cell : ℤ) :
    let packet := (actualErCell admissible ledger.val ledger.property.1 state cell).withSources
      (apSmoothJet admissible 2 cell source.1) (apSmoothJet admissible 1 cell source.2.1)
      (apSmoothJet admissible 1 cell source.2.2)
    packet.ZeroOrder ∧ packet.SecondOrder := by
  have force := congrArg (fun value : SmoothCapSource L parameters.sigma0 parameters.gamma ell =>
    apSmoothJet admissible 2 cell value.1) rows
  have determinant := congrArg (fun value : SmoothCapSource L parameters.sigma0 parameters.gamma ell =>
    apSmoothJet admissible 1 cell value.2.1) rows
  have third := congrArg (fun value : SmoothCapSource L parameters.sigma0 parameters.gamma ell =>
    apSmoothJet admissible 1 cell value.2.2) rows
  have same := ErCell.withSources_eq (actualErCell admissible ledger.val ledger.property.1 state cell)
    (apSmoothJet admissible 2 cell source.1) (apSmoothJet admissible 1 cell source.2.1)
    (apSmoothJet admissible 1 cell source.2.2) force determinant third
  exact (congrArg (fun packet : ErCell => packet.ZeroOrder ∧ packet.SecondOrder) same).mpr
    (actualErCell_reduction admissible ledger.val ledger.property.1 state mean cell)

end Grad.CartesianUncompressed
