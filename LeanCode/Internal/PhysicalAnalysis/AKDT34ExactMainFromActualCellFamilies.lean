import AKDT33ActualEventualPhysicalFamily
import MainFromPhysicalFamily

noncomputable section
open Set

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalFamily Grad.MainAssembly
open Grad.PhysicalFamily.SampledThresholdFamily
open Grad.MainAssembly.SampledAxisChartConstruction

/-- The unchanged main statement now follows from actual analytic cell
families alone. All physical geometry is constructed in this block, and the
existing exact axis/moduli consumer supplies the remaining target clauses. -/
theorem exact_main_of_actual_cell_families
    (constructed : ∀ length : ℝ, 0 < length → CellSolutionFamily length) :
    mainTheoremStatement := by
  intro length positive
  let family := constructed length positive
  obtain ⟨threshold, thresholdLarge, physicalAfter⟩ := actual_eventual_physical_family length positive family
  apply packMainWitnessFromSampledAxisChartData length family.rho family.delta family.alpha family.lower family.upper
    threshold positive family.rhoPositive family.rhoSmall family.deltaNonzero family.alphaNonresonant
    family.lowerPositive family.intervalNontrivial family.upperSmall
    ((firstSampledPeriod_positive length family).trans thresholdLarge)
    (exactSampledTargetFamily length family)
  · intro period after
    exact ⟨exactSampledTargetFamily_smooth length family period (thresholdLarge.trans after), physicalAfter period after⟩
  · intro period after parameter
    exact exactSampledTargetFamily_hasSampledAxisChartSeedData length family period (thresholdLarge.trans after)
      parameter (physicalAfter period after parameter)

end Grad.PhysicalGeometry
