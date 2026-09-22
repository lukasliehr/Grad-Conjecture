import AKAY13ActualDivDivResolventEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.TensorBootstrap

/-- The checked weak div-div equation and the actual compatible contractions
give H1 membership of the SAME original L2 field. -/
theorem startupSameField_divDiv_h1 (kernels : TensorIndex → FieldL2 →L[ℂ] FieldL2)
    (regular : FieldH1 →L[ℂ] FieldH1)
    (compatible : ∀ field, valueInclusion (regular field) =
      startupSecondKernelSumFor kernels (valueInclusion field))
    (coarseSmall : ‖startupSecondKernelSumFor kernels‖ < 1) (fineSmall : ‖regular‖ < 1)
    (original zeroth : FieldL2) (flux : Fin 2 → FieldL2)
    (equation : Laplacian.laplacian (distributionEmbedding original) =
      (∑ index : TensorIndex,
        distributionDerivative index.1 (distributionDerivative index.2 (distributionEmbedding (kernels index original)))) +
      distributionEmbedding zeroth +
      ∑ coordinate : Fin 2, distributionDerivative coordinate (distributionEmbedding (flux coordinate))) :
    ∃ field : FieldH1, valueInclusion field = original := by
  have coarseNorm : ‖(-(startupSecondKernelSumFor kernels)).restrictScalars ℝ‖ ≤
      ‖startupSecondKernelSumFor kernels‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro field
    change ‖-startupSecondKernelSumFor kernels field‖ ≤ ‖startupSecondKernelSumFor kernels‖ * ‖field‖
    rw [norm_neg]
    exact (startupSecondKernelSumFor kernels).le_opNorm field
  have fineNorm : ‖(-regular).restrictScalars ℝ‖ ≤ ‖regular‖ := by
    refine ContinuousLinearMap.opNorm_le_bound ((-regular).restrictScalars ℝ) (norm_nonneg regular) ?_
    intro field
    change ‖-regular field‖ ≤ ‖regular‖ * ‖field‖
    rw [norm_neg]
    exact regular.le_opNorm field
  let coarse := (-(startupSecondKernelSumFor kernels)).restrictScalars ℝ
  let fine := (-regular).restrictScalars ℝ
  let remainder := startupDivDivRemainder original zeroth flux
  let candidate := Grad.Foundations.neumannInverse fine remainder
  have compatibleNeg (field : FieldH1) : valueInclusion (fine field) = coarse (valueInclusion field) := by
    change valueInclusion (-regular field) = -startupSecondKernelSumFor kernels (valueInclusion field)
    rw [map_neg, compatible]
  have fineRight : candidate - fine candidate = remainder :=
    congrArg (fun operator : FieldH1 →L[ℝ] FieldH1 => operator remainder)
      (Grad.Foundations.neumannInverse_right fine (fineNorm.trans_lt fineSmall))
  have coarseLeft (field : FieldL2) :
      Grad.Foundations.neumannInverse coarse (field - coarse field) = field :=
    congrArg (fun operator : FieldL2 →L[ℝ] FieldL2 => operator field)
      (Grad.Foundations.neumannInverse_left coarse (coarseNorm.trans_lt coarseSmall))
  have candidateEquation : valueInclusion candidate - coarse (valueInclusion candidate) = valueInclusion remainder := by
    rw [← compatibleNeg, ← map_sub, fineRight]
  have originalEquation : original - coarse original = valueInclusion remainder := by
    change original - (-startupSecondKernelSumFor kernels original) = _
    rw [sub_neg_eq_add]
    exact startupSameField_divDiv_resolvent kernels original zeroth flux equation
  have same := congrArg (fun field : FieldL2 => Grad.Foundations.neumannInverse coarse field)
    (candidateEquation.trans originalEquation.symm)
  rw [coarseLeft, coarseLeft] at same
  exact ⟨candidate, same⟩

end Grad.CartesianStartup
