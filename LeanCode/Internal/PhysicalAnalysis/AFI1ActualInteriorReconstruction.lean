import ANF9OriginalTraceCoherence
import ANK5ActualDeterminantConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualReferenceAssembly
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearDivision
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Envelope
open Grad.ActualAngularInverse Grad.ActualNonexceptionalInverse Grad.RawCircularSectors
open Grad.ActualScalarForcing Grad.ActualScalarResidual
variable {L sigma gamma ell : ℝ}

/-- The actual AN15 scalar equation on the original AP smooth carrier. -/
def ActualScalarEquation (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell) : Prop :=
  ∀ cell : ℤ, -laplacianJet (apSmoothJet admissible 1 cell theta) +
    ((((cell : ℝ) * ell / L) ^ 2 : ℝ) : ℂ) • apSmoothJet admissible 1 cell (apFullB admissible theta) =
      apSmoothJet admissible 1 cell (scalarForcing admissible source)

theorem actualScalarEquation_determinant (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source)
    (equation : ActualScalarEquation admissible theta source) :
    circularDeterminant admissible (reconstructedState admissible theta source) = source.2.1 :=
  actualReconstructedDeterminant admissible theta source thetaExcluded sourceExcluded
    (scalarEquation_annihilates_actualResidual admissible theta source thetaExcluded sourceExcluded equation)

theorem reconstructedState_allInteriorRows (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (compatible : source ∈ smoothCapSourceCore admissible)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source)
    (equation : ActualScalarEquation admissible theta source) :
    circularRows admissible (reconstructedState admissible theta source) = source :=
  Prod.ext (reconstructedState_force admissible theta source compatible
    (reconstructionLoad_nonresonant admissible theta source thetaExcluded sourceExcluded))
    (Prod.ext (actualScalarEquation_determinant admissible theta source thetaExcluded sourceExcluded equation)
      (reconstructedState_third admissible theta source compatible))

/-- One actual original-domain state solves all three interior rows and has
all five native graph slots; the scalar PDE is the only remaining interior input. -/
theorem actualInteriorReconstruction (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (compatible : source ∈ smoothCapSourceCore admissible)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source)
    (thetaFlat : APSmoothAxisFirstJetZero admissible theta)
    (equation : ActualScalarEquation admissible theta source) :
    ∃ state : CompensatedData L sigma gamma ell,
      state.1 = theta ∧ state ∈ circularCompensatedCore admissible ∧ AvoidsExceptionalState state ∧
      circularRows admissible state = source ∧
      ∀ grade : ℕ, compensatedNorm admissible grade state ≤
        reconstructionConstant L gamma grade *
          (‖apSmoothGrade L sigma gamma ell 1 (grade + 2) theta‖ +
            ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) source.1‖ +
            ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) source.2.2‖) :=
  ⟨reconstructedState admissible theta source, rfl,
    reconstructedState_circularCore admissible theta source compatible thetaExcluded sourceExcluded thetaFlat,
    reconstructedState_excluded admissible theta source thetaExcluded sourceExcluded,
    reconstructedState_allInteriorRows admissible theta source compatible thetaExcluded sourceExcluded equation,
    reconstructedState_native_bound admissible theta source compatible
      (reconstructionLoad_nonresonant admissible theta source thetaExcluded sourceExcluded)⟩

end Grad.ActualReferenceAssembly
