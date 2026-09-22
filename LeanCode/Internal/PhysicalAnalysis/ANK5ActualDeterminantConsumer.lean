import ANK4OriginalScalarInjectivity

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

/-- The transformed residual determines the original projected determinant row
on any actual raw-excluded state. Its residual support is proved here. -/
theorem actualDeterminant_of_literalMultiplier (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell) (source : SmoothCapSource L sigma gamma ell)
    (stateExcluded : AvoidsExceptionalState state) (sourceExcluded : AvoidsExceptionalSource source)
    (equation :
      let residual := apSmoothDiv admissible (compensatedReconstruct admissible state) + source.2.1
      residual + (4 : ℂ) • apShiftInverse admissible 0 (apShiftInverse admissible 0 residual) = 0) :
    circularDeterminant admissible state = source.2.1 := by
  let divergence := apSmoothDiv admissible (compensatedReconstruct admissible state)
  have divergenceExcluded := state_divergence_excluded admissible state stateExcluded
  have residualExcluded := scalarExcluded_add admissible divergence source.2.1 divergenceExcluded
    (source_scalar_excluded admissible source sourceExcluded)
  have residualZero := literalAPMultiplier_eq_zero admissible (divergence + source.2.1)
    (fun cell => residualExcluded cell 2 (Or.inr (Or.inl rfl)))
    (fun cell => residualExcluded cell (-2) (Or.inr (Or.inr rfl))) equation
  change -(apSmoothRemoveMean L sigma gamma ell 1 divergence) = source.2.1
  rw [scalarExcluded_removeMean admissible divergence divergenceExcluded,
    eq_neg_of_add_eq_zero_left residualZero, neg_neg]

/-- Exact ANV consumer. No support assumption is imposed on the determinant
residual or on the reconstructed state; both follow from the actual inputs. -/
theorem actualReconstructedDeterminant (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source)
    (equation :
      let residual := apSmoothDiv admissible
        (compensatedReconstruct admissible (reconstructedState admissible theta source)) + source.2.1
      residual + (4 : ℂ) • apShiftInverse admissible 0 (apShiftInverse admissible 0 residual) = 0) :
    circularDeterminant admissible (reconstructedState admissible theta source) = source.2.1 :=
  actualDeterminant_of_literalMultiplier admissible _ source
    (reconstructedState_excluded admissible theta source thetaExcluded sourceExcluded) sourceExcluded equation

end Grad.ActualScalarResidual
