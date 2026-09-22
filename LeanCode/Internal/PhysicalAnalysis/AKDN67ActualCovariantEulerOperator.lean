import AKDN13ActualPhysicalRowEulerAllocation
import AKDD20ActualNormalizedRowsOriginalPhase

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularWeightedSmoothness Grad.AnnularRadialSmoothness
open Grad.GaugeCoefficients.Physical.Allocation

variable {source target : ℕ} {parameters : PhaseParameters} {length compact : ℝ}
    {kernel : (state : AnnularReconstructionState parameters length compact) →
      (radius : RadialPoint) → RadialKernel parameters radius source target}

/-- The same finite reserve argument applies to the actual reconstructed
covariant family; the reserve cancels before any quantitative estimate. -/
theorem actualEulerFamily_finiteOperator
    (family : ActualEulerFamily parameters length compact kernel)
    (state : AnnularReconstructionState parameters length compact) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (smooth : SmoothConjugatedFamily parameters lower positive bounded.le (kernel state))
    (grade order : ℕ) :
    ∃ reserve : ℕ,
      ContDiffOn ℝ order (radialConjugatedAction parameters lower positive bounded.le
        (kernel state) grade reserve) (Icc lower 1) ∧
      ∀ rank ≤ order, ∀ radius : RadialPoint, radius.val ∈ Icc lower 1 →
        vectorEulerWithinIteratedDerivative (Icc lower 1) rank
          (radialConjugatedAction parameters lower positive bounded.le (kernel state) grade reserve) radius.val =
        conjugatedKernelAction parameters grade reserve radius
          (conjugatedEulerKernel parameters radius (fun k => family.kernels state k radius) rank) := by
  obtain ⟨reserve,regular⟩ := smooth grade order
  have operatorSmooth : ContDiffOn ℝ order
      (radialConjugatedAction parameters lower positive bounded.le (kernel state) grade reserve) (Icc lower 1) :=
    regular.congr (fun _ _ => rfl)
  have same : family.kernels state 0=kernel state := funext (family.zero state)
  refine ⟨reserve,operatorSmooth,?_⟩
  intro rank rankLe radius inside
  have regularRank : ContDiffOn ℝ rank
      (radialConjugatedAction parameters lower positive bounded.le (family.kernels state 0) grade reserve) (Icc lower 1) := by
    rw [same]
    exact operatorSmooth.of_le (by exact_mod_cast rankLe)
  have actual := genuineConjugatedOperatorEuler parameters lower positive bounded (family.kernels state)
    (family.derivative state lower positive bounded) grade reserve rank regularRank radius inside
  rw [same] at actual
  exact actual

/-- Joint coefficient/input orders of the genuine original-phase covariant
Euler action, with precisely one high coefficient in either branch. -/
theorem actualEulerFamily_action_complementary
    (family : ActualEulerFamily parameters length compact kernel) (rank grade : ℕ) :
    ∃ first second : ℝ, 0≤first ∧ 0≤second ∧
    ∀ state : RetainedInverseState parameters length compact,
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ (radius : RadialPoint) (high low : CellL2 source),
    (∀ mode, high mode=(annularFrequency mode.1 mode.2 : ℂ)^grade • low mode) →
    ‖bulkKernelAction parameters grade radius
      (conjugatedEulerKernel parameters radius (fun order => family.kernels state.val order radius) rank) high‖ ≤
      2^grade*(first*(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+rank))*‖high‖+
        second*(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+(rank+grade)))*‖low‖) := by
  obtain ⟨first,first0,firstBound⟩ := family.moments.conjugatedKernels rank 0
  obtain ⟨second,second0,secondBound⟩ := family.moments.conjugatedKernels rank grade
  refine ⟨first,second,first0,second0,?_⟩
  intro state unit radius high low same
  apply (nativeBalancedAction_bound parameters grade radius _ high low same).trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num : (0:ℝ)≤2) grade)
  exact add_le_add (mul_le_mul_of_nonneg_right (by simpa only [Nat.add_zero] using firstBound state.val unit radius) (norm_nonneg high))
    (mul_le_mul_of_nonneg_right (secondBound state.val unit radius) (norm_nonneg low))

end Grad.OriginalCartesianTameEstimate
