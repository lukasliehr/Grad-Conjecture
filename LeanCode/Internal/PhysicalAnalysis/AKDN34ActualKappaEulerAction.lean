import AKDN33FiniteTerminalEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularWeightedSmoothness Grad.AnnularRadialSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.GaugeCoefficients.Physical.Allocation

/-- The genuine original-phase Euler kernel of each of the three actual
kappa factors in the prescribed G3 source. -/
def actualSourceConjugatedKappaEulerKernel (parameters : PhaseParameters) (length compact : ℝ)
    (component : Fin 3) (state : AnnularReconstructionState parameters length compact)
    (rank : ℕ) (radius : RadialPoint) : RadialKernel parameters radius 1 1 :=
  conjugatedEulerKernel parameters radius
    (fun order => (actualSourceKappaEulerFamily parameters length compact component).kernels state order radius) rank

theorem actualSourceKappaEulerAction_complementary (parameters : PhaseParameters) (length compact : ℝ)
    (component : Fin 3) (rank grade : ℕ) :
    ∃ first second : ℝ, 0 ≤ first ∧ 0 ≤ second ∧
    ∀ state : RetainedInverseState parameters length compact,
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ (radius : RadialPoint) (high low : CellL2 1),
    (∀ mode, high mode=(annularFrequency mode.1 mode.2 : ℂ)^grade • low mode) →
    ‖bulkKernelAction parameters grade radius
      (actualSourceConjugatedKappaEulerKernel parameters length compact component state.val rank radius) high‖ ≤
      2^grade*(first*(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+rank))*‖high‖+
        second*(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+(rank+grade)))*‖low‖) := by
  have moments : OriginalEulerMoments parameters length compact
      (actualSourceConjugatedKappaEulerKernel parameters length compact component) :=
    (actualSourceKappaEulerFamily parameters length compact component).moments.conjugatedKernels
  obtain ⟨first,first0,firstBound⟩ := moments rank 0
  obtain ⟨second,second0,secondBound⟩ := moments rank grade
  refine ⟨first,second,first0,second0,?_⟩
  intro state unit radius high low same
  apply (nativeBalancedAction_bound parameters grade radius _ high low same).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (2:ℝ)^grade)
  exact add_le_add
    (mul_le_mul_of_nonneg_right (by simpa only [Nat.add_zero] using firstBound state.val unit radius) (norm_nonneg _))
    (mul_le_mul_of_nonneg_right (secondBound state.val unit radius) (norm_nonneg _))

/-- One finite reserve differentiates every required kappa order. The
reserve is only a regularity device and cancels on the same input family. -/
theorem actualSourceKappaOperator_finiteEuler (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (component : Fin 3) (grade order : ℕ) :
    ∃ reserve : ℕ,
    ContDiffOn ℝ order (radialConjugatedAction parameters lower positive bounded.le
      (actualSourceKappaKernel parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low component)
      grade reserve) (Icc lower 1) ∧
    ∀ rank ≤ order, ∀ radius : RadialPoint, radius.val ∈ Icc lower 1 →
      vectorEulerWithinIteratedDerivative (Icc lower 1) rank
        (radialConjugatedAction parameters lower positive bounded.le
          (actualSourceKappaKernel parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low component)
          grade reserve) radius.val =
        conjugatedKernelAction parameters grade reserve radius
          (actualSourceConjugatedKappaEulerKernel parameters length compact component state.val rank radius) := by
  let family := actualSourceKappaEulerFamily parameters length compact component
  obtain ⟨reserve,smooth⟩ := actualSourceKappaKernel_smooth parameters length state.val.val.rho state.val.val.epsilon
    state.val.val.field state.val.val.low lower positive bounded component grade order
  have same : family.kernels state.val 0 =
      actualSourceKappaKernel parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low component :=
    funext (family.zero state.val)
  refine ⟨reserve,smooth,?_⟩
  intro rank rankLe radius inside
  have regular : ContDiffOn ℝ rank (radialConjugatedAction parameters lower positive bounded.le
      (family.kernels state.val 0) grade reserve) (Icc lower 1) := by
    rw [same]
    exact smooth.of_le (by exact_mod_cast rankLe)
  have actual := genuineConjugatedOperatorEuler parameters lower positive bounded (family.kernels state.val)
    (family.derivative state.val lower positive bounded) grade reserve rank regular radius inside
  rw [same] at actual
  exact actual

end Grad.OriginalCartesianTameEstimate
