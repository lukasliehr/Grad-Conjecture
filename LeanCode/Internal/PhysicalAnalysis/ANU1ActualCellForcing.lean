import ANK5ActualDeterminantConsumer
import ANF9OriginalTraceCoherence
import ANB20LiteralScalarBoundaryConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualForcingSupport
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.ActualAngularInverse Grad.ActualNonexceptionalInverse Grad.ActualScalarForcing
open Grad.CartesianScalarElimination Grad.BoundedScalarInverse
variable {L sigma gamma ell : ℝ}

theorem forceResponse_jet (admissible : Admissible L sigma gamma ell)
    (force : APSmooth L sigma gamma ell 2) (cell : ℤ) :
    apSmoothJet admissible 2 cell (forceResponse admissible force) =
      -vectorInverseJet (apSmoothJet admissible 2 cell force) :=
  ((apSmoothJet admissible 2 cell).map_neg _).trans
    (congrArg Neg.neg (apVectorInverse_jet admissible force cell))

theorem forceRadial_jet (admissible : Admissible L sigma gamma ell)
    (force : APSmooth L sigma gamma ell 2) (cell : ℤ) :
    apSmoothJet admissible 1 cell (forceRadial admissible force) =
      vectorRadialJet (-vectorInverseJet (apSmoothJet admissible 2 cell force)) :=
  (radial_planarLift_jet admissible (forceResponse admissible force) cell).trans
    (congrArg (fun jet : ClosedJet 2 => apProductJet radialRowJet (valueMapJet planarInclusionMap jet))
      (forceResponse_jet admissible force cell))

theorem scalarForcingInput_jet (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (cell : ℤ) :
    apSmoothJet admissible 1 cell (scalarForcingInput admissible source) =
      apSmoothJet admissible 1 cell source.2.1 +
        vectorDivJet (-vectorInverseJet (apSmoothJet admissible 2 cell source.1)) +
          seedScaledFrequency L ell cell • shiftInverseJet 0 (apSmoothJet admissible 1 cell source.2.2) := by
  let project := apSmoothJet admissible 1 cell
  have divergence := (div_planarLift_jet admissible (forceResponse admissible source.1) cell).trans
    (congrArg (fun jet : ClosedJet 2 => planarDivJet (valueMapJet planarInclusionMap jet))
      (forceResponse_jet admissible source.1 cell))
  have axial := (apSmoothAxial_jet admissible (reconstructedScalar admissible source.2.2) cell).trans
    (congrArg (fun jet : ClosedJet 1 => seedScaledFrequency L ell cell • jet)
      (apShiftInverse_jet admissible 0 source.2.2 cell))
  exact (project.map_add (source.2.1 + apSmoothDiv admissible (forceLift admissible source.1))
      (apSmoothAxial L sigma gamma ell 1 (reconstructedScalar admissible source.2.2))).trans
    (congrArg₂ (fun first second : ClosedJet 1 => first + second)
      ((project.map_add source.2.1 (apSmoothDiv admissible (forceLift admissible source.1))).trans
        (congrArg (fun jet : ClosedJet 1 => project source.2.1 + jet) (divergence.trans (vectorDivJet_actual _).symm))) axial)

theorem scalarForcing_jet (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (cell : ℤ) :
    apSmoothJet admissible 1 cell (scalarForcing admissible source) =
      fullBJet (apSmoothJet admissible 1 cell source.2.1 +
        vectorDivJet (-vectorInverseJet (apSmoothJet admissible 2 cell source.1)) +
          seedScaledFrequency L ell cell • shiftInverseJet 0 (apSmoothJet admissible 1 cell source.2.2)) :=
  (apFullB_jet admissible (scalarForcingInput admissible source) cell).trans
    (congrArg fullBJet (scalarForcingInput_jet admissible source cell))

end Grad.ActualForcingSupport
