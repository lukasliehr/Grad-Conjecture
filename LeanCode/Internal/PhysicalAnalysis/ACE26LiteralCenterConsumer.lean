import ACE25ActualPinnedCenterSolution

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.NonlinearDivision (closedOrigin laplacianJet laplacianJet_value)

/-- Exact AN6a specification, expressed solely through the original closed
values and Cartesian derivatives. All equations include the boundary. -/
def IsPinnedCenterSolution (mode : ℤ) (frequency : ℝ) (source solution : ClosedJet 1) : Prop :=
  angularClosedJet mode solution = solution ∧
  solution.value closedOrigin = 0 ∧
  (∀ direction : Fin 2, closedDerivative solution 1 (fun _ => direction) closedOrigin = 0) ∧
  ∀ point : ClosedDisk,
    closedDerivative solution 2 (fun _ => 0) point + closedDerivative solution 2 (fun _ => 1) point +
      ((3 * frequency ^ 2 : ℝ) : ℂ) • solution.value point = -source.value point

theorem pinnedCenterSolution_specification (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (frequency : ℝ) (source : ClosedJet 1) (pure : angularClosedJet mode source = source) :
    IsPinnedCenterSolution mode frequency source (pinnedCenterSolution mode frequency source) := by
  refine ⟨pinnedCenterSolution_pure mode center frequency source pure,
    (pinnedCenterSolution_pinned mode frequency source).1, ?_, ?_⟩
  · intro direction
    exact (pinnedCenterSolution_pinned mode frequency source).2 direction
  · exact pinnedCenterSolution_literal mode center frequency source pure

theorem pinnedCenterSolution_literal_unique (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (frequency : ℝ) (source : ClosedJet 1) (pure : angularClosedJet mode source = source)
    (candidate : ClosedJet 1) (solution : IsPinnedCenterSolution mode frequency source candidate) :
    candidate = pinnedCenterSolution mode frequency source := by
  have pinned : CenterPinned candidate := ⟨solution.2.1, solution.2.2.1⟩
  have equation : laplacianJet candidate + ((3 * frequency ^ 2 : ℝ) : ℂ) • candidate = -source := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    simpa only [closedJet_value_add, closedJet_value_smul, closedJet_value_neg, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, ContinuousMap.neg_apply, laplacianJet_value, laplacianCoefficient] using solution.2.2.2 point
  exact pinnedCenterSolution_unique mode center frequency source pure candidate solution.1 pinned equation

/-- Immediate public consumer: one actual smooth scalar jet, the same pure
source, the original closed disk, and uniqueness with the literal first jet. -/
theorem actual_center_scalar_solver (mode : ℤ) (center : mode = 1 ∨ mode = -1) (frequency : ℝ)
    (source : ClosedJet 1) (pure : angularClosedJet mode source = source) :
    ∃! solution : ClosedJet 1, IsPinnedCenterSolution mode frequency source solution := by
  exact ⟨pinnedCenterSolution mode frequency source,
    pinnedCenterSolution_specification mode center frequency source pure,
    fun candidate specification => pinnedCenterSolution_literal_unique mode center frequency source pure candidate specification⟩

end Grad.ActualCenterVolterra
