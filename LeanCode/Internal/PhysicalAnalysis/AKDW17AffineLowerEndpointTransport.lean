import AKDW13ActualNativeAxialGraphBound
import AKDW15KnownTensorOriginalCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
namespace Grad.CartesianStartup.StartupAdjustableSpatialGraph
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets Grad.NonlinearProduct
open Grad.OriginalCoreRealization Grad.OriginalCartesianTameEstimate Grad.NonlinearQuotientBounds

/-- Affine actual tensors retain the adjustable unknown endpoint, while
all known-source terms are paid independently at the same rank. -/
theorem transportAffineEndpoint {State : Type*} {parameters : PhaseParameters} {order grade : ℕ}
    {budget : State → ℝ} {kernel : State → StartupL2 3 →L[ℂ] StartupL2 3}
    {ranked : State → StartupL2 (startupTensorDimension 3 grade) →L[ℂ] StartupL2 (startupTensorDimension 3 grade)}
    (actual : StartupUniformOriginalEndpoint parameters budget kernel ranked) (budgetNonnegative : ∀ state,0≤budget state)
    (cores images known : State → ACore parameters 3)
    (same : ∀ state,originalSourceFieldLinear parameters (images state)=kernel state (originalSourceFieldLinear parameters (cores state)))
    (payment : State → ℝ) (paid : ∀ state,originalGradeNorm grade (known state)≤payment state)
    {field : State → StartupL2 3}
    (lower : StartupAdjustableSpatialGraph order field
      (fun state => originalGradeNorm grade (images state+known state))
      (fun state => originalCellNorm parameters grade (images state+known state))) :
    StartupAdjustableSpatialGraph order field (fun state => originalGradeNorm grade (cores state))
      (fun state => originalCellNorm parameters grade (cores state)+budget state*originalGradeNorm 0 (cores state)+payment state) := by
  intro epsilon positive
  obtain ⟨delta,deltaPositive,transport⟩ := actual.absorbLower budgetNonnegative epsilon positive
  obtain ⟨remainder,remainderNonnegative,lowerBound⟩ := lower delta deltaPositive
  obtain ⟨constant,nonnegative,bounded⟩ := transport remainder remainderNonnegative
  refine ⟨constant+(delta+remainder),add_nonneg nonnegative (add_nonneg deltaPositive.le remainderNonnegative),?_⟩
  intro state
  let graph := (lowerBound state).choose
  have graphSame := (lowerBound state).choose_spec.1
  have graphBound := (lowerBound state).choose_spec.2
  have highSum : originalGradeNorm grade (images state+known state)≤
      originalGradeNorm grade (images state)+originalGradeNorm grade (known state) :=
    originalGradeNorm_add_le grade (images state) (known state)
  have knownCell : originalCellNorm parameters grade (known state)≤originalGradeNorm grade (known state) :=
    startupOriginalCellNorm_le_full parameters grade (known state)
  have cellSum : originalCellNorm parameters grade (images state+known state)≤
      originalCellNorm parameters grade (images state)+originalGradeNorm grade (known state) := by
    exact le_trans (startupOriginalCellNorm_add parameters grade (images state) (known state))
      (add_le_add (le_refl (originalCellNorm parameters grade (images state))) knownCell)
  have split : ‖graph‖≤delta*(originalGradeNorm grade (images state)+originalGradeNorm grade (known state))+
      remainder*(originalCellNorm parameters grade (images state)+originalGradeNorm grade (known state)) := by
    exact le_trans graphBound (add_le_add
      (mul_le_mul_of_nonneg_left highSum deltaPositive.le)
      (mul_le_mul_of_nonneg_left cellSum remainderNonnegative))
  have inputBound : ‖graph‖-(delta+remainder)*originalGradeNorm grade (known state)≤
      delta*originalGradeNorm grade (images state)+remainder*originalCellNorm parameters grade (images state) := by
    nlinarith only [split]
  have inputPaid := bounded state (cores state) (images state)
    (‖graph‖-(delta+remainder)*originalGradeNorm grade (known state)) (same state) inputBound
  have sourcePaid := mul_le_mul_of_nonneg_left (paid state) (add_nonneg deltaPositive.le remainderNonnegative)
  have low0 : 0≤originalCellNorm parameters grade (cores state)+budget state*originalGradeNorm 0 (cores state) :=
    add_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (budgetNonnegative state) (originalGradeNorm_nonnegative 0 (cores state)))
  have payment0 : 0≤payment state := (originalGradeNorm_nonnegative grade (known state)).trans (paid state)
  refine ⟨graph,graphSame,?_⟩
  nlinarith only [inputPaid,sourcePaid,mul_nonneg (add_nonneg deltaPositive.le remainderNonnegative) low0,mul_nonneg nonnegative payment0]

end Grad.CartesianStartup.StartupAdjustableSpatialGraph
