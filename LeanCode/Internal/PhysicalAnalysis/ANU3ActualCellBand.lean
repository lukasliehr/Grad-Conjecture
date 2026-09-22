import ANU2ActualAngularSupport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualForcingSupport
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.ActualAngularInverse Grad.ActualNonexceptionalInverse Grad.ActualScalarForcing
open Grad.CartesianScalarElimination Grad.BoundedScalarInverse
variable {L sigma gamma ell : ℝ}

/-- Literal support of all three original cap-source components in AN36. -/
abbrev OriginalCapSourceBand (admissible : Admissible L sigma gamma ell)
    (ceiling : ℝ) (source : SmoothCapSource L sigma gamma ell) : Prop :=
  ∀ cell, ¬ InCellBand L ell ceiling cell →
    apSmoothJet admissible 2 cell source.1 = 0 ∧ apSmoothJet admissible 1 cell source.2.1 = 0 ∧
      apSmoothJet admissible 1 cell source.2.2 = 0

theorem forceRadial_cell_zero (admissible : Admissible L sigma gamma ell)
    (force : APSmooth L sigma gamma ell 2) (cell : ℤ) (zero : apSmoothJet admissible 2 cell force = 0) :
    apSmoothJet admissible 1 cell (forceRadial admissible force) = 0 := by
  have inverseZero := (congrArg vectorInverseJet zero).trans (map_zero vectorInverseJetLinear)
  have negativeZero := (congrArg Neg.neg inverseZero).trans neg_zero
  exact (forceRadial_jet admissible force cell).trans
    ((congrArg vectorRadialJet negativeZero).trans (map_zero vectorRadialLinear))

theorem scalarForcing_band (admissible : Admissible L sigma gamma ell)
    (ceiling : ℝ) (source : SmoothCapSource L sigma gamma ell) (supported : OriginalCapSourceBand admissible ceiling source) :
    OriginalSourceBand admissible ceiling (scalarForcing admissible source) := by
  intro cell outside
  have absent := supported cell outside
  have inverseZero := (congrArg vectorInverseJet absent.1).trans (map_zero vectorInverseJetLinear)
  have divZero := (congrArg vectorDivJet ((congrArg Neg.neg inverseZero).trans neg_zero)).trans (map_zero vectorDivLinear)
  have primitiveZero := (congrArg (shiftInverseJet 0) absent.2.2).trans (map_zero (shiftInverseLinear 1 0))
  have inputZero : apSmoothJet admissible 1 cell source.2.1 +
      vectorDivJet (-vectorInverseJet (apSmoothJet admissible 2 cell source.1)) +
        seedScaledFrequency L ell cell • shiftInverseJet 0 (apSmoothJet admissible 1 cell source.2.2) = 0 := by
    rw [absent.2.1, divZero, primitiveZero, smul_zero, add_zero, add_zero]
  exact (scalarForcing_jet admissible source cell).trans ((congrArg fullBJet inputZero).trans (map_zero fullBLinear))

end Grad.ActualForcingSupport
