import AKDT32ActualPhysicalConclusions
import SampledThresholdFamily

noncomputable section
open Set

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalFamily
open Grad.PhysicalFamily.SampledThresholdFamily

/-- The actual physical provider for the identical total sampled family,
with one enlarged integer threshold and no geometric input. -/
theorem actual_eventual_physical_family (length : ℝ) (positive : 0 < length)
    (family : CellSolutionFamily length) :
    ∃ threshold : ℕ, firstSampledPeriod length family ≤ threshold ∧
      ∀ period : ℕ, threshold ≤ period → ∀ parameter : Icc family.lower family.upper,
        PhysicalConclusions (exactSampledTargetFamily length family period parameter) length period := by
  obtain ⟨physicalPeriod, _, physicalAfter⟩ := exists_sampledPhysicalConclusionsThreshold length positive family
  refine ⟨max (firstSampledPeriod length family) physicalPeriod, le_max_left _ _, ?_⟩
  intro period after parameter
  have sampledAfter : firstSampledPeriod length family ≤ period := (le_max_left _ _).trans after
  rw [exactSampledTargetFamily_eq length family period sampledAfter]
  exact (physicalAfter period ((le_max_right _ _).trans after)).2
    (sampledEpsilon_mem_after_firstPeriod length family period sampledAfter) 0 parameter

end Grad.PhysicalGeometry
