import AKBZ21SharpFullPhaseBlockPayment
import AKAA11LiteralDerivativeKernelAction

noncomputable section
set_option maxHeartbeats 1100000
open MeasureTheory MeasureTheory.Measure
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.CartesianState Grad.NonlinearProduct Grad.GenericCarriers

theorem phase_sum_fin_eq_Icc {Value : Type*} [AddCommMonoid Value] (rank : ℕ) (function : ℕ → Value) :
    (∑ displacement : Fin rank,function (displacement.val+1))=∑ displacement ∈ Finset.Icc 1 rank,function displacement := by
  classical
  apply Finset.sum_bij (fun displacement _ => displacement.val+1)
  · intro displacement membership
    exact Finset.mem_Icc.mpr ⟨Nat.succ_pos _,Nat.succ_le_iff.mpr displacement.isLt⟩
  · intro first firstMem second secondMem same
    apply Fin.ext
    omega
  · intro displacement membership
    have bounds := Finset.mem_Icc.mp membership
    refine ⟨⟨displacement-1,by omega⟩,Finset.mem_univ _,?_⟩
    dsimp
    omega
  · intro displacement membership
    rfl

/-- The already accepted coarse normalization and the sharp decomposition
are exactly the same continuous coefficient after restoring input moments. -/
theorem sharpAllocatedCoefficient_sameCoarse {L sigma gamma ell : ℝ}
    {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (rank : ℕ) (positive : 0<rank)
    (word : Fin rank → Fin 2) (index : CartesianMultiIndex) (input shift : ℤ) :
    (∑ displacement : Fin rank,
      ((scaledCellWeight L ell input^(rank-(displacement.val+1)):ℝ):ℂ) •
        sharpAllocatedCoefficient family rank (displacement.val+1) word index input shift)=
    ((scaledCellWeight L ell input^(rank-1):ℝ):ℂ) •
      startupAllocatedCoefficient (family (cartesianOrder index+rank)) rank word
        (sharpCoefficientIndex index rank) input shift := by
  apply ContinuousMap.ext
  intro point
  simp only [ContinuousMap.sum_apply,ContinuousMap.smul_apply]
  rw [phase_sum_fin_eq_Icc rank (fun displacement =>
    ((scaledCellWeight L ell input^(rank-displacement):ℝ):ℂ) •
      sharpAllocatedCoefficient family rank displacement word index input shift point)]
  rw [sharpAllocatedCoefficient_exact family rank positive word index input shift point]
  rw [←startupAllocatedCoefficient_unreserve]
  rw [coherent_derivative_raw family coherent]
  rfl

/-- The exact same allocation identity at the genuine original disk L2
operator, including its action on an arbitrary input coordinate. -/
theorem sharpAllocatedOperator_sameCoarse {L sigma gamma ell : ℝ}
    {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (rank : ℕ) (positive : 0<rank)
    (word : Fin rank → Fin 2) (index : CartesianMultiIndex) (input shift : ℤ)
    (field : DiskL2 inputDimension) :
    (∑ displacement : Fin rank,
      closedOperatorL2 (sharpAllocatedCoefficient family rank (displacement.val+1) word index input shift)
        (((scaledCellWeight L ell input^(rank-(displacement.val+1)):ℝ):ℂ) • field))=
    closedOperatorL2
      (startupAllocatedCoefficient (family (cartesianOrder index+rank)) rank word
        (sharpCoefficientIndex index rank) input shift)
      (((scaledCellWeight L ell input^(rank-1):ℝ):ℂ) • field) := by
  have same := congrArg (fun coefficient : C(ClosedDisk,OperatorValue inputDimension outputDimension) =>
    closedOperatorAction inputDimension outputDimension coefficient field)
    (sharpAllocatedCoefficient_sameCoarse family coherent rank positive word index input shift)
  simp only [_root_.map_sum,map_smul,_root_.sum_apply,_root_.smul_apply] at same
  have applied (coefficient : C(ClosedDisk,OperatorValue inputDimension outputDimension)) :
      closedOperatorAction inputDimension outputDimension coefficient=closedOperatorL2 coefficient := rfl
  simp_rw [applied] at same
  simpa only [map_smul] using same

end Grad.OriginalCartesianTameEstimate
