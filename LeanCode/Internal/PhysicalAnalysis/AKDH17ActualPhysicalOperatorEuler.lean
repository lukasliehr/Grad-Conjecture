import AKDH16GenuineConjugatedOperatorEuler

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularWeightedSmoothness Grad.AnnularRadialSmoothness
open Grad.AnnularCurrentLow
open Grad.GaugeCoefficients.Physical.Allocation

/-- Every genuine Euler derivative of the SAME original physical row
operator is exactly its sharp full-cell kernel. The finite input reserve
comes from the accepted regularity theorem and disappears on compatible
inputs through the exact reserve law. -/
theorem samePhysicalOperator_genuineEuler (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (row : Fin 3) (grade rank : ℕ) :
    ∃ reserve : ℕ, ∀ (radius : RadialPoint), radius.val ∈ Icc lower 1 →
      vectorEulerWithinIteratedDerivative (Icc lower 1) rank
        (radialConjugatedAction parameters lower positive bounded.le
          (lowPhysicalRowKernel parameters L compact state row) grade reserve) radius.val =
        conjugatedKernelAction parameters grade reserve radius
          (actualPhysicalConjugatedEulerKernel parameters L compact row state.val rank radius) := by
  obtain ⟨reserve,smooth⟩ := originalPhysicalRowKernel_finiteOrder parameters L compact state lower positive bounded row grade rank
  have same : physicalRowEulerKernel parameters L compact row state.val 0 =
      lowPhysicalRowKernel parameters L compact state row := by
    funext radius
    exact physicalRowEulerKernel_zero parameters L compact row state radius
  refine ⟨reserve,?_⟩
  intro radius inside
  have regular : ContDiffOn ℝ rank
      (radialConjugatedAction parameters lower positive bounded.le
        (physicalRowEulerKernel parameters L compact row state.val 0) grade reserve) (Icc lower 1) := by
    rwa [same]
  have actual := genuineConjugatedOperatorEuler parameters lower positive bounded
    (physicalRowEulerKernel parameters L compact row state.val)
    (physicalRowEulerKernel_derivative parameters L compact row state.val lower positive bounded)
    grade reserve rank regular radius inside
  rw [same] at actual
  exact actual

/-- The literal derivative has the complementary coefficient/input bound,
with no cost from the auxiliary regularity reserve. -/
theorem samePhysicalOperator_EulerAction (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (row : Fin 3) (rank grade : ℕ) :
    ∃ first second : ℝ, 0 ≤ first ∧ 0 ≤ second ∧
    ∀ (state : RetainedInverseState parameters L compact),
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∃ reserve : ℕ, ∀ (radius : RadialPoint), radius.val ∈ Icc lower 1 →
    ∀ (reserved high low : CellL2 7),
    (∀ mode, reserved mode = (annularFrequency mode.1 mode.2 : ℂ)^reserve • high mode) →
    (∀ mode, high mode = (annularFrequency mode.1 mode.2 : ℂ)^grade • low mode) →
    ‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (radialConjugatedAction parameters lower positive bounded.le
        (lowPhysicalRowKernel parameters L compact state row) grade reserve) radius.val reserved‖ ≤
      2^grade *
        (first*(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+rank))*‖high‖+
          second*(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+(rank+grade)))*‖low‖) := by
  obtain ⟨first,second,first0,second0,bound⟩ := actualPhysicalEulerAction_complementary parameters L compact row rank grade
  refine ⟨first,second,first0,second0,?_⟩
  intro state unit
  obtain ⟨reserve,same⟩ := samePhysicalOperator_genuineEuler parameters L compact state lower positive bounded row grade rank
  refine ⟨reserve,?_⟩
  intro radius inside reserved high low sameReserve sameGrade
  rw [same radius inside,conjugatedKernelAction_same parameters grade reserve radius _ reserved high sameReserve]
  exact bound state unit radius high low sameGrade

end Grad.OriginalCartesianTameEstimate
