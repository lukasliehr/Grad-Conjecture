import ANV12ActualCircularDomain

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualNonexceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra Grad.ActualAngularInverse
open Grad.RawCircularSectors
variable {L sigma gamma ell : ℝ}

/-- AN12/AN13 reconstruction on the actual original source and domain. One
state is chosen before the grade. Its force and third row are exact, and its
five original graph slots have no grade or analytic-width loss. The scalar
second-row equation and radial boundary condition are separate consumers. -/
theorem actualNonexceptionalReconstruction (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (compatible : source ∈ smoothCapSourceCore admissible)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source)
    (thetaFlat : APSmoothAxisFirstJetZero admissible theta) :
    ∃ state : CompensatedData L sigma gamma ell,
      state.1 = theta ∧ state ∈ circularCompensatedCore admissible ∧
      circularForce admissible state = source.1 ∧ circularThird admissible state = source.2.2 ∧
      (∀ grade : ℕ, compensatedNorm admissible grade state ≤
        reconstructionConstant L gamma grade *
          (‖apSmoothGrade L sigma gamma ell 1 (grade + 2) theta‖ +
            ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) source.1‖ +
            ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) source.2.2‖)) := by
  have nonresonant := reconstructionLoad_nonresonant admissible theta source thetaExcluded sourceExcluded
  exact ⟨reconstructedState admissible theta source, rfl,
    reconstructedState_circularCore admissible theta source compatible thetaExcluded sourceExcluded thetaFlat,
    reconstructedState_force admissible theta source compatible nonresonant,
    reconstructedState_third admissible theta source compatible,
    reconstructedState_native_bound admissible theta source compatible nonresonant⟩

end Grad.ActualNonexceptionalInverse
