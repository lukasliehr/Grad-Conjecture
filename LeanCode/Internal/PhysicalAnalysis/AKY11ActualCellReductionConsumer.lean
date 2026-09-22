import AKY10ExactSecondOrderSplit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.CartesianUncompressed
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Frame Grad.NonlinearDivision Grad.NonlinearRange

/-- One original full cell of the actual three-row equation and its quotient.
The two scalar coefficient terms c and h_3 are different coordinates. -/
structure ErCell where
  frequency : ℂ
  theta : ClosedJet 1
  vector : ClosedJet 2
  scalar : ClosedJet 1
  force : ClosedJet 2
  determinant : ClosedJet 1
  third : ClosedJet 1
  forceCorrection : ClosedJet 2
  thirdCorrection : ClosedJet 1
  fluxPlanar : ClosedJet 2
  fluxScalar : ClosedJet 1

variable {L sigma gamma ell : ℝ}

def actualErCell (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (state : CompensatedData L sigma gamma ell) (cell : ℤ) : ErCell where
  frequency := seedScaledFrequency L ell cell
  theta := apSmoothJet admissible 1 cell state.1
  vector := apSmoothJet admissible 2 cell (apSmoothPlanar L sigma gamma ell (actualErQuotient admissible state))
  scalar := apSmoothJet admissible 1 cell (apSmoothScalar L sigma gamma ell (actualErQuotient admissible state))
  force := apSmoothJet admissible 2 cell (actualForce admissible data coherent state)
  determinant := apSmoothJet admissible 1 cell (actualDeterminant admissible data coherent state)
  third := apSmoothJet admissible 1 cell (actualThird admissible data coherent state)
  forceCorrection := apSmoothJet admissible 2 cell (actualErForceCorrection admissible data coherent
    (compensatedReconstruct admissible state))
  thirdCorrection := apSmoothJet admissible 1 cell (actualErThirdCorrection admissible data coherent
    (compensatedReconstruct admissible state))
  fluxPlanar := vectorMeanFreeLinear (apSmoothJet admissible 2 cell
    (apSmoothPlanar L sigma gamma ell (actualErFlux admissible data coherent (compensatedReconstruct admissible state))))
  fluxScalar := scalarMeanFreeLinear (apSmoothJet admissible 1 cell
    (apSmoothScalar L sigma gamma ell (actualErFlux admissible data coherent (compensatedReconstruct admissible state))))

def ErCell.SecondOrder (cell : ErCell) : Prop :=
  planarLaplacian 2 cell.vector = erPlanarPrincipal cell.fluxPlanar cell.forceCorrection +
    erPlanarMixed cell.frequency cell.scalar cell.fluxScalar + erPlanarSource cell.force cell.determinant ∧
  laplacianJet cell.scalar = erScalarPrincipal cell.thirdCorrection +
    erScalarMixed cell.frequency cell.vector cell.forceCorrection + erScalarSource cell.frequency cell.force cell.third

def ErCell.ZeroOrder (cell : ErCell) : Prop :=
  equivariantAverageJet cell.vector = radialMeanSourceLinear (cell.force - cell.forceCorrection) ∧
  gradientJet cell.theta = recoveredGradientLinear cell.vector + covariantAngularInverse (cell.force - cell.forceCorrection) ∧
  cell.scalar = cell.frequency • cell.theta + scalarAngularInverse (cell.third + cell.thirdCorrection)

/-- Dependency-ready ER4/ER10–13 consumer of the actual GQF full-cell physical
rows. The only smooth scalar premise is its original angular mean. -/
theorem actualErCell_reduction (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (state : CompensatedData L sigma gamma ell)
    (mean : APSmoothMeanZero admissible state.1) (cell : ℤ) :
    (actualErCell admissible data coherent state cell).ZeroOrder ∧
      (actualErCell admissible data coherent state cell).SecondOrder := by
  let packet := actualErCell admissible data coherent state cell
  have gauges := actualQuotient_fullCell_gauges admissible state cell
  have force := actualForce_fullCell admissible data coherent state mean cell
  have third := actualThird_fullCell admissible data coherent state mean cell
  have determinant := actualDeterminant_fullCell admissible data coherent state cell
  constructor
  · exact ⟨actual_radial_mean_recovery packet.theta packet.vector packet.force packet.forceCorrection force,
      actual_gradient_recovery packet.theta packet.vector packet.force packet.forceCorrection (mean cell) force,
      actual_scalar_recovery packet.frequency packet.theta packet.scalar packet.third packet.thirdCorrection
        (mean cell) gauges.2 third⟩
  · exact uncompressed_secondOrder_system packet.frequency packet.theta packet.scalar packet.determinant packet.third
      packet.fluxScalar packet.thirdCorrection packet.vector packet.force packet.forceCorrection packet.fluxPlanar
      (mean cell) gauges.2 gauges.1 (scalarMeanFree_zeroMean _) (vectorMeanFree_zeroMean _) force third determinant

end Grad.CartesianUncompressed
