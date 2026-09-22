import ANU1ActualCellForcing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualForcingSupport
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.ActualAngularInverse Grad.ActualNonexceptionalInverse Grad.ActualScalarForcing
open Grad.CartesianScalarElimination Grad.BoundedScalarInverse Grad.RawCircularSectors Grad.ActualScalarResidual
variable {L sigma gamma ell : ℝ}

theorem responseDivergence_excluded (mode : ℤ) (force : ClosedJet 2) (excluded : rawVectorJet mode force = 0) :
    angularClosedJet mode (vectorDivJet (-vectorInverseJet force)) = 0 := by
  have inverseZero := (rawVectorJet_vectorInverse mode force).trans
    ((congrArg vectorInverseJet excluded).trans (map_zero vectorInverseJetLinear))
  have divZero := (vectorDivJet_rawVector mode (vectorInverseJet force)).symm.trans
    ((congrArg vectorDivJet inverseZero).trans (map_zero vectorDivLinear))
  change angularClosedJetLinear 1 mode (vectorDivLinear (-vectorInverseJet force)) = 0
  rw [map_neg, map_neg]
  change -angularClosedJet mode (vectorDivJet (vectorInverseJet force)) = 0
  rw [divZero, neg_zero]

private theorem inputAngular_support (mode : ℤ) (frequency : ℂ)
    (force : ClosedJet 2) (second third : ClosedJet 1)
    (forceAbsent : rawVectorJet mode force = 0) (secondAbsent : angularClosedJet mode second = 0)
    (thirdAbsent : angularClosedJet mode third = 0) :
    angularClosedJet mode (second + vectorDivJet (-vectorInverseJet force) + frequency • shiftInverseJet 0 third) = 0 := by
  have primitiveAbsent := (shiftInverseJet_angular 0 mode third).symm.trans
    ((congrArg (shiftInverseJet 0) thirdAbsent).trans (map_zero (shiftInverseLinear 1 0)))
  rw [angularClosedJet_add, angularClosedJet_add, angularClosedJet_smul,
    secondAbsent, responseDivergence_excluded mode force forceAbsent, primitiveAbsent, smul_zero, add_zero, add_zero]

theorem scalarForcingInput_excluded (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (excluded : AvoidsExceptionalSource source) :
    ScalarAvoidsExceptional admissible (scalarForcingInput admissible source) := by
  intro cell mode exceptional
  have absent := rawSource_excluded_components admissible mode source (excluded mode exceptional) cell
  exact (congrArg (angularClosedJet mode) (scalarForcingInput_jet admissible source cell)).trans
    (inputAngular_support mode (seedScaledFrequency L ell cell) _ _ _ absent.1 absent.2.1 absent.2.2)

/-- The actual AN15 source meets the scalar solver's exact mode exclusions. -/
theorem scalarForcing_nonexceptional (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (excluded : AvoidsExceptionalSource source) :
    OriginalSourceNonexceptional admissible (scalarForcing admissible source) := by
  have absent := scalarForcingInput_excluded admissible source excluded
  have modes (cell mode : ℤ) (exceptional : IsExceptionalRaw mode) :
      angularClosedJet mode (apSmoothJet admissible 1 cell (scalarForcing admissible source)) = 0 := by
    have original : apSmoothJet admissible 1 cell (scalarForcing admissible source) =
        fullBJet (apSmoothJet admissible 1 cell (scalarForcingInput admissible source)) :=
      apFullB_jet admissible (scalarForcingInput admissible source) cell
    exact (congrArg (angularClosedJet mode) original).trans
      ((fullBJet_angular mode _).trans ((congrArg fullBJet (absent cell mode exceptional)).trans (map_zero fullBLinear)))
  intro cell
  exact ⟨modes cell 0 (Or.inl rfl), modes cell 2 (Or.inr (Or.inl rfl)), modes cell (-2) (Or.inr (Or.inr rfl))⟩

end Grad.ActualForcingSupport
