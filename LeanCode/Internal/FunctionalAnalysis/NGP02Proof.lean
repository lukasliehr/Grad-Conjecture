import NGP02Interface

noncomputable section

namespace Grad.CartesianState

open Grad.ClosedJets
open Grad.DiskExtension.Operator

local instance ngp02ProofCellPeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩

theorem physicalCollarExtensionBlock : PhysicalCollarExtensionGoal := by
  intro dimension
  refine ⟨(fun field => periodizedExtension field), rfl, ?_, ?_, ?_, ?_⟩
  · intro grade
    exact ⟨physicalExtensionCNormFactor grade,
      physicalExtensionCNormFactor_nonnegative grade,
      fun field => collarPhysicalCNorm_periodizedExtension_bound field grade⟩
  · intro field order point
    exact periodizedExtension_preserves_physical_jet field point
  · intro field reality
    exact periodizedExtension_preserves_reality field reality
  · intro field point cell
    exact torusPhysicalCollarLift_periodic (periodizedExtension field) point cell

end Grad.CartesianState
