import NGP02Proof

noncomputable section

namespace Grad.CartesianState

open Grad.ClosedJets
open Grad.DiskExtension.Operator

local instance ngp02ConsumerCellPeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩

/-- The fixed physical candidate used downstream for an already constructed
analytic parameter derivative. -/
def physicalParameterDerivativeCandidate {dimension : ℕ}
    (analyticDerivative : DiskCellClosedJet dimension) :
    TorusSmoothField dimension :=
  periodizedExtension analyticDerivative

/-- Immediate NG_CAL107-facing consumer: the actual candidate uses the one
fixed extension, retains every disk jet, has the all-order collar bound, and
is periodic (and real whenever its analytic jet is real). -/
theorem physicalParameterDerivativeCandidate_consumer
    {dimension grade : ℕ}
    (analyticDerivative : DiskCellClosedJet dimension) :
    collarPhysicalCNorm
        (physicalParameterDerivativeCandidate analyticDerivative) grade ≤
      physicalExtensionCNormFactor grade *
        closedPhysicalCNorm analyticDerivative grade ∧
    (∀ (order : ℕ) (point : DiskCellDomain),
      torusPhysicalOperatorDerivative
          (physicalParameterDerivativeCandidate analyticDerivative) order
          (diskToTorus point) =
        closedPhysicalOperatorDerivative analyticDerivative order point) ∧
    (∀ (point : PhysicalCollar) (cell : ℝ),
      torusPhysicalCollarLift
          (physicalParameterDerivativeCandidate analyticDerivative) point
          (cell + 2 * Real.pi) =
        torusPhysicalCollarLift
          (physicalParameterDerivativeCandidate analyticDerivative) point cell) ∧
    (IsRealDiskCellField analyticDerivative →
      IsRealTorusField
        (physicalParameterDerivativeCandidate analyticDerivative)) := by
  refine ⟨collarPhysicalCNorm_periodizedExtension_bound
      analyticDerivative grade, ?_, ?_, ?_⟩
  · intro order point
    exact periodizedExtension_preserves_physical_jet analyticDerivative point
  · intro point cell
    exact torusPhysicalCollarLift_periodic
      (periodizedExtension analyticDerivative) point cell
  · intro reality
    exact periodizedExtension_preserves_reality analyticDerivative reality

end Grad.CartesianState
