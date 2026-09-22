import GQC30APSmoothFaithfulness

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.GaugeTransfer

def apSmoothRotation {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension : ℕ) : APSmooth L sigma gamma ell dimension →ₗ[ℂ] APSmooth L sigma gamma ell dimension :=
  (apSmoothCoordinate admissible dimension 0).comp (apSmoothPartial admissible dimension 1) -
    (apSmoothCoordinate admissible dimension 1).comp (apSmoothPartial admissible dimension 0)

theorem apSmoothRotation_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension) (cell : ℤ) :
    apSmoothJet admissible dimension cell (apSmoothRotation admissible dimension field) =
      Grad.NonlinearRange.rotationJet (apSmoothJet admissible dimension cell field) := by
  change apSmoothJet admissible dimension cell
    (apSmoothCoordinate admissible dimension 0 (apSmoothPartial admissible dimension 1 field) -
      apSmoothCoordinate admissible dimension 1 (apSmoothPartial admissible dimension 0 field)) = _
  exact (map_sub (apSmoothJet admissible dimension cell) _ _).trans
    (congrArg₂ (fun first second : ClosedJet dimension => first - second)
      ((apSmoothCoordinate_jet admissible 0 (apSmoothPartial admissible dimension 1 field) cell).trans
        (congrArg (Grad.NonlinearQuotientBounds.coordinateJet 0)
          (apSmoothPartial_jet admissible field 1 cell)))
      ((apSmoothCoordinate_jet admissible 1 (apSmoothPartial admissible dimension 0 field) cell).trans
        (congrArg (Grad.NonlinearQuotientBounds.coordinateJet 1)
          (apSmoothPartial_jet admissible field 0 cell))))

theorem apSmoothRotation_weak {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension) (grade : ℕ) :
    APHasAngularDerivative L sigma gamma ell (apSmoothGrade L sigma gamma ell dimension grade field)
      (apSmoothGrade L sigma gamma ell dimension grade (apSmoothRotation admissible dimension field)) := by
  intro cell testCell vector test smooth compact supported
  rw [← apSmoothJet_l2 admissible (apSmoothRotation admissible dimension field) grade cell,
    ← apSmoothJet_l2 admissible field grade cell, apSmoothRotation_jet]
  exact rotationJet_weak _ testCell vector test smooth compact supported

/-- The extra compensated rotation norm of the actual removed complement
is same-grade. Its derivative is proved, not postulated as graph data. -/
theorem apSmoothRotation_removed {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) (grade : ℕ)
    (member : apSmoothGrade L sigma gamma ell 3 grade field ∈ apComplementRange L sigma gamma ell grade) :
    apSmoothGrade L sigma gamma ell 3 grade (apSmoothRotation admissible 3 field) =
      apStoredQuarter L sigma gamma ell grade (apSmoothGrade L sigma gamma ell 3 grade field) ∧
      ‖apSmoothGrade L sigma gamma ell 3 grade (apSmoothRotation admissible 3 field)‖ ≤
        ‖apSmoothGrade L sigma gamma ell 3 grade field‖ := by
  have identity := (apSmoothRotation_weak admissible field grade).unique
    (apComplementRange_angular_weak L sigma gamma ell grade _ member)
  exact ⟨identity, identity ▸ apStoredQuarter_bound L sigma gamma ell grade _⟩

end Grad.GaugeCoefficients.Physical.Compensated
