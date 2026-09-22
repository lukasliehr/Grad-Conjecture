import AFI3ActualRadialResidual
import ANU5ActualScalarSolverAdapter

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualReferenceAssembly
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Envelope
open Grad.BoundaryTrace Grad.CircularHighWeak Grad.ActualSmoothRobin Grad.CartesianScalarElimination
open Grad.ActualScalarForcing Grad.ActualNonexceptionalInverse Grad.RawCircularSectors
open Grad.ActualForcingSupport Grad.BoundedScalarInverse
variable {L sigma gamma ell : ℝ}

theorem angularHighJet_coefficient (mode : ℤ) (high : 3 ≤ |mode|) (field : ClosedJet 1) :
    angularClosedJet mode (excludedAngularJet lowAngularModes field) = angularClosedJet mode field := by
  change angularClosedJetLinear 1 mode (field - selectedAngularJet lowAngularModes field) = _
  rw [map_sub]
  change angularClosedJet mode field - angularClosedJet mode (selectedAngularJet lowAngularModes field) = _
  rw [angularClosedJet_selected, if_neg (highMode_not_low mode high), sub_zero]

theorem highRobin_coefficient (mode : ℤ) (high : 3 ≤ |mode|) (field : ClosedJet 1) :
    angularClosedJet mode (robinResidualJet (excludedAngularJet lowAngularModes field)) =
      angularClosedJet mode (eulerJet field + (2 : ℂ) • field) := by
  simp only [robinResidualJet, angularClosedJet_add, angularClosedJet_smul, angularClosedJet_euler]
  rw [angularHighJet_coefficient mode high field]

private theorem robin_sum_algebra {E : Type*} [AddCommGroup E] [Module ℂ E]
    (first boundary forcing : E) (scalar : ℂ) (equation : first = scalar • (boundary - forcing)) :
    first + scalar • forcing = scalar • boundary := by
  rw [equation, smul_sub]
  abel

/-- The exact original scalar Robin equation gives the actual physical
circular boundary row. Low components of arbitrary beta are discarded by the
paper's prescribed high boundary projection. -/
theorem actualScalarSolution_boundary (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source)
    (beta : BandSmoothBoundary L sigma gamma ell)
    (laws : IsOriginalScalarSolution admissible (scalarForcing admissible source) (forcedBoundary admissible source beta) theta)
    (grade : ℕ) :
    circularCoreTrace admissible grade (reconstructedState admissible theta source) =
      apHighProjection L sigma gamma ell (grade + 1) (beta.grade grade) := by
  let trace := circularCoreTrace admissible grade (reconstructedState admissible theta source)
  have sameB : boundaryB L sigma gamma ell (grade + 1) trace = boundaryB L sigma gamma ell (grade + 1) (beta.grade grade) := by
    apply originalBoundary_ext (grade + 1)
    intro pair
    by_cases high : 3 ≤ |pair.1|
    · have robin := original_scalar_literal_robin admissible (scalarForcing admissible source)
        (forcedBoundary admissible source beta) theta laws pair.2 pair.1 grade
      rw [boundaryCoefficient_angular, highRobin_coefficient pair.1 high, forcedBoundary_coefficient] at robin
      exact (actualCircularTrace_B_coefficient admissible grade theta source thetaExcluded sourceExcluded pair high).trans
        ((robin_sum_algebra _ _ _ _ robin).trans (boundaryB_coefficient (grade + 1) (beta.grade grade) pair).symm)
    · have scalar : (highMultiplier pair.1 : ℂ) = 0 := by
        rw [highMultiplier, if_pos (not_highMode_low pair.1 high)]
        rfl
      have first := boundaryB_coefficient (grade + 1) trace pair
      have second := boundaryB_coefficient (grade + 1) (beta.grade grade) pair
      rw [scalar, zero_smul] at first second
      exact first.trans second.symm
  exact boundaryB_high_injective (grade + 1) trace (apHighProjection L sigma gamma ell (grade + 1) (beta.grade grade))
    (apHighProjection_idempotent L sigma gamma ell (grade + 1) _)
    (apHighProjection_idempotent L sigma gamma ell (grade + 1) _)
    (sameB.trans (boundaryB_highProjection (grade + 1) (beta.grade grade)).symm)

end Grad.ActualReferenceAssembly
