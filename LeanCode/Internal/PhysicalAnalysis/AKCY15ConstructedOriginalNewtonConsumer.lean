import AKCY14SameOriginalNewtonExactZero
import NewtonFiniteChoice

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3500

namespace Grad.NashMoser.OriginalIteration
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.SmoothingFamily Grad.Q24Realization Grad.NashMoser.OriginalLimit Grad.NashMoser.Numeric
open Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}

namespace OriginalNewtonInverse
variable (inverse : OriginalNewtonInverse neighborhood cellLength loss)

/-- The accepted explicit finite maximum chooses every scale guard from
actual smoothing/nonlinear/inverse constants. No numerical smallness datum
is supplied and no high-grade supremum is used. -/
def chosenScale (lossLarge : 6 ≤ loss) : OriginalNewtonScale inverse := by
  let guards := chosenInitial_guards neighborhood.radius (inverse.correctionConstant loss)
    (inverse.quadraticConstant lossLarge) (inverse.defectConstant lossLarge (initialCutoff loss)) loss
    neighborhood.radiusPositive
    ((by norm_num : (0:ℝ) ≤ 1).trans (inverse.correctionConstant_one_le loss))
    ((by norm_num : (0:ℝ) ≤ 1).trans (inverse.quadraticConstant_one_le lossLarge))
    ((by norm_num : (0:ℝ) ≤ 1).trans (inverse.defectConstant_one_le lossLarge _))
  exact ⟨lossLarge, chosenInitial neighborhood.radius (inverse.correctionConstant loss)
    (inverse.quadraticConstant lossLarge) (inverse.defectConstant lossLarge (initialCutoff loss)) loss,
    guards.1, guards.2.2.1, guards.2.2.2.1, guards.2.2.2.2⟩

theorem chosenScale_threshold_positive (lossLarge : 6 ≤ loss) :
    0 < (inverse.chosenScale lossLarge).initial ^ (-initialDecay loss) :=
  Real.rpow_pos_of_pos (by linarith [(inverse.chosenScale lossLarge).initialLarge]) _

theorem chosenScale_contains_zero (lossLarge : 6 ≤ loss) (finite : OriginalFiniteParameter)
    (member : finite ∈ neighborhood.parameterDomain)
    (seedZero : originalNonlinearSource parameters cellLength reference inside finite 0 = 0) :
    finite ∈ (inverse.chosenScale lossLarge).parameterDomain := by
  refine ⟨member,?_⟩
  change sourceSize parameters base loss
    (originalNonlinearSource parameters cellLength reference inside finite 0) ≤ _
  rw [seedZero,map_zero]
  exact (inverse.chosenScale_threshold_positive lossLarge).le

/-- SAME-original existence from the actual enriched Newton construction.
The only remaining analytic input is the displayed PC inverse on the fixed
original low product; actual recurrence and original-core limit are proved. -/
theorem constructed_original_solution (lossLarge : 6 ≤ loss)
    (finite : (inverse.chosenScale lossLarge).parameterDomain) :
    ∃ state : stateSmoothRange parameters reference inside,
      stateSize parameters reference inside base loss state ≤ neighborhood.radius/2 ∧
      originalNonlinearSource parameters cellLength reference inside finite.val state = 0 :=
  ⟨(inverse.chosenScale lossLarge).originalLimit finite,
    (inverse.chosenScale lossLarge).originalLimit_low finite,
    (inverse.chosenScale lossLarge).originalLimit_exact_zero finite⟩

/-- Literal physical fixed-reference quotient equation, with every original
source row and original chart/core value retained. -/
theorem constructed_original_physical_equation (lossLarge : 6 ≤ loss)
    (finite : (inverse.chosenScale lossLarge).parameterDomain) :
    physicalFixedSliceMap parameters cellLength reference inside finite.val.1
      (neighborhood.patchInside (neighborhood.seedInside finite.val finite.property.1))
      ((finite.val.2:ℂ),smoothingChartCore parameters
        ((inverse.chosenScale lossLarge).originalLimit finite).val) = 0 := by
  have zero := congrArg (fun source : sourceSmoothRange parameters => source.val)
    ((inverse.chosenScale lossLarge).originalLimit_exact_zero finite)
  rw [originalNonlinearSource_value parameters cellLength reference inside finite.val
    ((inverse.chosenScale lossLarge).originalLimit finite)
    (neighborhood.patchInside (neighborhood.seedInside finite.val finite.property.1))
    ((inverse.chosenScale lossLarge).originalLimit_axis finite)] at zero
  exact zero

end OriginalNewtonInverse
end Grad.NashMoser.OriginalIteration
