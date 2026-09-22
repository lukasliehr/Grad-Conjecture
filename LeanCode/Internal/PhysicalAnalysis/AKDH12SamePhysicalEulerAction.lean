import AKDH11SameNativeBalancedCoordinatePDE
import AKCD2SameNativeBalancedAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularWeightedSmoothness Grad.AnnularRadialSmoothness
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularCurrentLow Grad.GaugeCoefficients.Physical.Allocation

def actualPhysicalConjugatedEulerKernel (parameters : PhaseParameters) (L compact : ℝ)
    (row : Fin 3) (state : AnnularReconstructionState parameters L compact) (rank : ℕ) (radius : RadialPoint) :
    RadialKernel parameters radius 7 1 :=
  conjugatedEulerKernel parameters radius (fun order => physicalRowEulerKernel parameters L compact row state order radius) rank

theorem actualPhysicalConjugatedEulerKernel_moments (parameters : PhaseParameters) (L compact : ℝ) (row : Fin 3) :
    OriginalEulerMoments parameters L compact (actualPhysicalConjugatedEulerKernel parameters L compact row) :=
  (physicalRowEulerKernel_moments parameters L compact row).conjugatedKernels

/-- The operator kernel is the literal Euler derivative of the original
phase-conjugated AEI14 row entry, for every input and output cell. -/
theorem actualPhysicalConjugatedEulerKernel_same (parameters : PhaseParameters) (L compact : ℝ)
    (row : Fin 3) (state : RetainedInverseState parameters L compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (radius : RadialPoint)
    (inside : radius.val ∈ Icc lower 1) (rank : ℕ) (shift input : ℤ × ℤ) :
    actualClosedConjugatedEulerEntry parameters (Icc lower 1)
      (fun point => (lowPhysicalRowKernel parameters L compact state row (collarRadius lower positive bounded.le point)).entry)
      rank radius.val shift input =
    radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 radius.val •
      (actualPhysicalConjugatedEulerKernel parameters L compact row state.val rank radius).entry shift input := by
  have actual := conjugatedEulerKernel_actual parameters lower positive bounded
    (physicalRowEulerKernel parameters L compact row state.val)
    (physicalRowEulerKernel_derivative parameters L compact row state.val lower positive bounded)
    radius inside rank shift input
  have same : (fun point => (physicalRowEulerKernel parameters L compact row state.val 0
      (collarRadius lower positive bounded.le point)).entry) =
      (fun point => (lowPhysicalRowKernel parameters L compact state row
        (collarRadius lower positive bounded.le point)).entry) := by
    funext point
    rw [physicalRowEulerKernel_zero]
  rw [same] at actual
  exact actual

/-- Complementary coefficient/input orders for actual differentiated rows.
The two coefficient orders are retained for the joint terminal allocation;
no successive coarse high-order operator bounds are multiplied. -/
theorem actualPhysicalEulerAction_complementary (parameters : PhaseParameters) (L compact : ℝ)
    (row : Fin 3) (rank grade : ℕ) :
    ∃ first second : ℝ, 0 ≤ first ∧ 0 ≤ second ∧
    ∀ (state : RetainedInverseState parameters L compact),
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ (radius : RadialPoint) (high low : CellL2 7),
    (∀ mode, high mode = (annularFrequency mode.1 mode.2 : ℂ)^grade • low mode) →
    ‖bulkKernelAction parameters grade radius
      (actualPhysicalConjugatedEulerKernel parameters L compact row state.val rank radius) high‖ ≤
      2^grade *
        (first*(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+rank))*‖high‖+
          second*(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+(rank+grade)))*‖low‖) := by
  obtain ⟨first,first0,firstBound⟩ := actualPhysicalConjugatedEulerKernel_moments parameters L compact row rank 0
  obtain ⟨second,second0,secondBound⟩ := actualPhysicalConjugatedEulerKernel_moments parameters L compact row rank grade
  refine ⟨first,second,first0,second0,?_⟩
  intro state unit radius high low same
  apply (nativeBalancedAction_bound parameters grade radius _ high low same).trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num : (0:ℝ)≤2) grade)
  exact add_le_add (mul_le_mul_of_nonneg_right (by simpa only [Nat.add_zero] using firstBound state.val unit radius) (norm_nonneg high))
    (mul_le_mul_of_nonneg_right (secondBound state.val unit radius) (norm_nonneg low))

end Grad.OriginalCartesianTameEstimate
