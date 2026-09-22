import MainFromCellSolutionFamily
import SampledAxisChartConstruction

noncomputable section

open Set

namespace Grad.MainAssembly.MainFromPhysicalFamily

open Grad.MainTarget
open Grad.PhysicalFamily
open Grad.PhysicalFamily.SampledThresholdFamily
open Grad.MainAssembly.MainFromCellSolutionFamily
open Grad.MainAssembly.SampledAxisChartConstruction

/-- Exact main-theorem consumer after eliminating the axis-chart package as an
independent assumption.  Its only remaining inputs are the actual analytic
cell family and the physical conclusions for the identical sampled maps. -/
theorem mainTheorem_of_cellSolutionFamilies_and_physical
    (constructed : ∀ cellLength : ℝ, 0 < cellLength →
      CellSolutionFamily cellLength)
    (physical :
      ∀ (cellLength : ℝ) (cellLengthPositive : 0 < cellLength),
        let cellFamily := constructed cellLength cellLengthPositive
        ∀ (period : ℕ),
          firstSampledPeriod cellLength cellFamily ≤ period →
          ∀ parameter : Set.Icc cellFamily.lower cellFamily.upper,
            PhysicalConclusions
              (exactSampledTargetFamily cellLength cellFamily period parameter)
              cellLength period) :
    mainTheoremStatement := by
  apply mainTheorem_of_cellSolutionFamilies constructed physical
  intro cellLength cellLengthPositive
  dsimp
  intro period periodAfter parameter
  exact exactSampledTargetFamily_hasSampledAxisChartSeedData cellLength
    (constructed cellLength cellLengthPositive) period periodAfter parameter
    (physical cellLength cellLengthPositive period periodAfter parameter)

end Grad.MainAssembly.MainFromPhysicalFamily
