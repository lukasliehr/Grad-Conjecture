import ANK3ActualReconstructedSupport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualScalarResidual
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.RawCircularSectors Grad.ActualNonexceptionalInverse Grad.ActualAngularInverse
variable {L sigma gamma ell : ℝ}

/-- Evaluation of the literal original AP expression, without a new multiplier
operator or a restriction of the analytic width. -/
theorem literalAPMultiplier_jet (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 1) (cell : ℤ) :
    apSmoothJet admissible 1 cell
        (field + (4 : ℂ) • apShiftInverse admissible 0 (apShiftInverse admissible 0 field)) =
      apSmoothJet admissible 1 cell field + (4 : ℂ) •
        shiftInverseJet 0 (shiftInverseJet 0 (apSmoothJet admissible 1 cell field)) := by
  let project := apSmoothJet admissible 1 cell
  have nested := (apShiftInverse_jet admissible 0 (apShiftInverse admissible 0 field) cell).trans
    (congrArg (shiftInverseJet 0) (apShiftInverse_jet admissible 0 field cell))
  exact (project.map_add field ((4 : ℂ) • apShiftInverse admissible 0 (apShiftInverse admissible 0 field))).trans
    (congrArg (fun value : ClosedJet 1 => project field + value)
      ((project.map_smul (4 : ℂ) _).trans (congrArg (fun value : ClosedJet 1 => (4 : ℂ) • value) nested)))

theorem literalAPMultiplier_eq_zero (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 1)
    (positive : ∀ cell, angularClosedJet 2 (apSmoothJet admissible 1 cell field) = 0)
    (negative : ∀ cell, angularClosedJet (-2) (apSmoothJet admissible 1 cell field) = 0)
    (kernel : field + (4 : ℂ) • apShiftInverse admissible 0 (apShiftInverse admissible 0 field) = 0) : field = 0 := by
  apply apSmoothJet_ext admissible
  intro cell
  have closedKernel := (literalAPMultiplier_jet admissible field cell).symm.trans
    ((congrArg (apSmoothJet admissible 1 cell) kernel).trans (map_zero _))
  exact (literalMultiplier_eq_zero _ (positive cell) (negative cell) closedKernel).trans (map_zero _).symm

theorem scalarExcluded_sub (admissible : Admissible L sigma gamma ell)
    (first second : APSmooth L sigma gamma ell 1)
    (firstExcluded : ScalarAvoidsExceptional admissible first) (secondExcluded : ScalarAvoidsExceptional admissible second) :
    ScalarAvoidsExceptional admissible (first - second) := by
  intro cell mode exceptional
  rw [map_sub]
  change angularClosedJetLinear 1 mode (_ - _) = 0
  rw [map_sub]
  change angularClosedJet mode (apSmoothJet admissible 1 cell first) -
    angularClosedJet mode (apSmoothJet admissible 1 cell second) = 0
  rw [firstExcluded cell mode exceptional, secondExcluded cell mode exceptional, sub_self]

private theorem multiplier_sub {E : Type*} [AddCommGroup E] [Module ℂ E]
    (inverse : E →ₗ[ℂ] E) (first second : E) :
    (first - second) + (4 : ℂ) • inverse (inverse (first - second)) =
      (first + (4 : ℂ) • inverse (inverse first)) - (second + (4 : ℂ) • inverse (inverse second)) := by
  rw [map_sub, map_sub, smul_sub]
  module

/-- Injectivity on the actual original-width nonexceptional scalar carrier. -/
theorem literalAPMultiplier_injective (admissible : Admissible L sigma gamma ell)
    (first second : APSmooth L sigma gamma ell 1)
    (firstExcluded : ScalarAvoidsExceptional admissible first) (secondExcluded : ScalarAvoidsExceptional admissible second)
    (same : first + (4 : ℂ) • apShiftInverse admissible 0 (apShiftInverse admissible 0 first) =
      second + (4 : ℂ) • apShiftInverse admissible 0 (apShiftInverse admissible 0 second)) : first = second := by
  have excluded := scalarExcluded_sub admissible first second firstExcluded secondExcluded
  have kernel : (first - second) + (4 : ℂ) • apShiftInverse admissible 0
      (apShiftInverse admissible 0 (first - second)) = 0 :=
    (multiplier_sub (apShiftInverseLinear admissible 1 0) first second).trans (sub_eq_zero.mpr same)
  exact sub_eq_zero.mp (literalAPMultiplier_eq_zero admissible _
    (fun cell => excluded cell 2 (Or.inr (Or.inl rfl)))
    (fun cell => excluded cell (-2) (Or.inr (Or.inr rfl))) kernel)

theorem scalarExcluded_removeMean (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 1) (excluded : ScalarAvoidsExceptional admissible field) :
    apSmoothRemoveMean L sigma gamma ell 1 field = field := by
  apply apSmoothJet_ext admissible
  intro cell
  rw [apSmoothRemoveMean_jet, excluded cell 0 (Or.inl rfl), sub_zero]

end Grad.ActualScalarResidual
