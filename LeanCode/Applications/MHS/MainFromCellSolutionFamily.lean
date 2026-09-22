import SampledMainAssemblySkeleton
import SampledThresholdFamily

noncomputable section

open Set

namespace Grad.MainAssembly.MainFromCellSolutionFamily

open Grad.MainTarget
open Grad.MainAssembly
open Grad.MainAssembly.PhysicalNormalHessian.Consumer
open Grad.MainAssembly.SampledAxisChartData
open Grad.PhysicalFamily
open Grad.PhysicalFamily.SampledThresholdFamily

/-- Exact main-theorem integration after integer sampling.  The analytic
branch is now represented only by an actual `CellSolutionFamily` inhabitant;
the remaining geometric inputs concern the identical canonical sampled
representatives. -/
theorem mainTheorem_of_cellSolutionFamilies
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
              cellLength period)
    (axisCharts :
      ∀ (cellLength : ℝ) (cellLengthPositive : 0 < cellLength),
        let cellFamily := constructed cellLength cellLengthPositive
        ∀ (period : ℕ),
          firstSampledPeriod cellLength cellFamily ≤ period →
          ∀ parameter : Set.Icc cellFamily.lower cellFamily.upper,
            HasSampledAxisChartSeedData
              (exactSampledTargetFamily cellLength cellFamily period parameter)
              (period * cellLength) period cellFamily.rho cellFamily.alpha
              cellFamily.delta parameter.val) :
    mainTheoremStatement := by
  intro cellLength cellLengthPositive
  let cellFamily := constructed cellLength cellLengthPositive
  apply packMainWitnessFromSampledAxisChartData cellLength cellFamily.rho
    cellFamily.delta cellFamily.alpha cellFamily.lower cellFamily.upper
    (firstSampledPeriod cellLength cellFamily) cellLengthPositive
    cellFamily.rhoPositive cellFamily.rhoSmall cellFamily.deltaNonzero
    cellFamily.alphaNonresonant cellFamily.lowerPositive
    cellFamily.intervalNontrivial cellFamily.upperSmall
    (firstSampledPeriod_positive cellLength cellFamily)
    (exactSampledTargetFamily cellLength cellFamily)
  · intro period periodAfter
    exact ⟨exactSampledTargetFamily_smooth cellLength cellFamily period
      periodAfter, physical cellLength cellLengthPositive period periodAfter⟩
  · intro period periodAfter parameter
    exact axisCharts cellLength cellLengthPositive period periodAfter parameter

end Grad.MainAssembly.MainFromCellSolutionFamily
