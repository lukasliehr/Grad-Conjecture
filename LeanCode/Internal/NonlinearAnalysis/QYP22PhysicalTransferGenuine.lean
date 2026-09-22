import Q23TransferProductGenuine
import PCO1PhysicalCoordinates

noncomputable section

open Filter
open scoped Topology

namespace Grad.PhysicalCoordinates

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct

/-- The exact physical permutation preserves the genuine newest-last transfer
derivative in every original field norm. -/
theorem physicalMixedTransferredVector_genuine
    (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (order : ℕ)
    (base : Q23MixedInput parameters)
    (directions : Fin (order + 1) → Q23MixedInput parameters)
    (inside : base.1 ∈ Seed.parameterDomain) (grade : ℕ) :
    Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ •
        (toPhysicalCore parameters (q23MixedTransferredVector parameters reference insideR order
            (base + t • directions (Fin.last order))
            (fun position => directions position.castSucc)) -
          toPhysicalCore parameters (q23MixedTransferredVector parameters reference insideR order base
            (fun position => directions position.castSucc)))) -
        toPhysicalCore parameters (q23MixedTransferredVector parameters reference insideR (order + 1)
          base directions)))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have actual := q23MixedTransferredVector_genuine parameters reference insideR order
    base directions inside grade
  simpa only [← map_sub, ← map_smul, toPhysicalCore_norm] using actual

end Grad.PhysicalCoordinates
