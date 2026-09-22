import AJD28ActualCoefficientCoordinateBounds
import AJD30UniformOperatorOperations
import BCI15FullBoundaryReferenceDeviation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.AnnularKernelOrbit Grad.AnnularInverseCalculus Grad.AnnularHighInverseOrbit
open Grad.BoundaryKernelAction Grad.ActualBoundaryInverse Grad.ActualBoundaryPrimitives
open Grad.GaugeCoefficients.Physical.Allocation

private theorem uniformBoundaryTower {Context : Type*} {E : Context → Type*}
    [∀ context, NormedAddCommGroup (E context)] [∀ context, NormedSpace ℝ (E context)]
    (budget : Context → ℕ → ℝ) (jet : (context : Context) → ℕ → ℕ → OrbitParameter → E context)
    (derivative : ∀ context angular cell point, HasFDerivAt (jet context angular cell)
      (orbitColumns (jet context (angular + 1) cell point) (jet context angular (cell + 1) point)) point)
    (bound : ∀ angular cell, ∃ constant : ℝ, 0 ≤ constant ∧ ∀ context point,
      ‖jet context angular cell point‖ ≤ constant * coordinateJetWeight (budget context) (angular + cell)) :
    UniformCoordinateBound budget (fun context => jet context 0 0) := by
  intro axis order
  obtain ⟨constant, nonnegative, estimate⟩ := bound (if axis then 0 else order) (if axis then order else 0)
  refine ⟨constant, nonnegative, ?_⟩
  intro context base time
  rw [iteratedDeriv_coordinateJet (jet context) (derivative context)]
  cases axis <;> simpa only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero] using estimate context (base + time • axisVector _)

/-- All jets of the actual boundary deviation carry the original primitive
factor; its zeroth value is uniformly bounded on the same B8 ball. -/
theorem actualBoundaryDeviation_uniformCoordinateBound (parameters : PhaseParameters) (L compact : ℝ) :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        fun tau => boundaryOrbitJetAction parameters 0 0 context.state.boundaryState.fullBoundaryDeviation tau 0 0) := by
  apply uniformBoundaryTower CoupledCoordinateContext.budget
    (fun context angular cell tau => boundaryOrbitJetAction parameters 0 0 context.state.boundaryState.fullBoundaryDeviation tau angular cell)
    (fun context angular cell tau => boundaryOrbitJetAction_hasFDerivAt parameters 0 0 context.state.boundaryState.fullBoundaryDeviation tau angular cell)
  intro angular cell
  obtain ⟨constant, nonnegative, bound⟩ := fullBoundaryDeviation_vanishingMoments parameters L compact (1 + (angular + cell))
  refine ⟨constant, nonnegative, ?_⟩
  intro context tau
  have moment := bound context.state.boundaryState
  change fullKernelMoment parameters (1 + (angular + cell)) context.state.boundaryState.fullBoundaryDeviation ≤
    constant * physicalBudget parameters context.state.val.val.field context.state.val.val.rho context.state.val.val.epsilon (1 + (angular + cell) + 7) at moment
  have actual := (boundaryOrbitJetAction_norm_le parameters 0 0 context.state.boundaryState.fullBoundaryDeviation tau angular cell).trans moment
  have primitive : ‖boundaryOrbitJetAction parameters 0 0 context.state.boundaryState.fullBoundaryDeviation tau angular cell‖ ≤
      constant * context.budget (angular + cell) := by
    simpa only [CoupledCoordinateContext.budget, show 1 + (angular + cell) + 7 = 8 + (angular + cell) by omega] using actual
  by_cases zero : angular + cell = 0
  · rw [coordinateJetWeight, if_pos zero, mul_one]
    rw [zero] at primitive
    exact primitive.trans ((mul_le_mul_of_nonneg_left context.budget_zero_le_one nonnegative).trans_eq (mul_one _))
  · simpa only [coordinateJetWeight, if_neg zero] using primitive
end Grad.AnnularCrossOrbit
