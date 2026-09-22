import AKAY12PhaseWeakConjugation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.TensorBootstrap Grad.SobolevBridge

theorem startupSecondKernelSumFor_distribution (kernels : TensorIndex → FieldL2 →L[ℂ] FieldL2)
    (field : FieldL2) :
    distributionEmbedding (startupSecondKernelSumFor kernels field) =
      distributionResolvent (∑ index : TensorIndex,
        distributionDerivative index.1 (distributionDerivative index.2 (distributionEmbedding (kernels index field)))) := by
  simp only [startupSecondKernelSumFor, sum_apply, ContinuousLinearMap.comp_apply, map_sum,
    startupSecondL2_distribution]

/-- The actual negative resolvent of a zeroth-order L2 source and a first-order L2 flux. -/
def startupDivDivRemainder (original zeroth : FieldL2) (flux : Fin 2 → FieldL2) : FieldH1 :=
  negativeResolvent (l2ToNegative (original - zeroth) -
    ∑ coordinate : Fin 2, derivativeToNegative coordinate (flux coordinate))

theorem startupDivDivRemainder_distribution (original zeroth : FieldL2) (flux : Fin 2 → FieldL2) :
    distributionEmbedding (valueInclusion (startupDivDivRemainder original zeroth flux)) =
      distributionResolvent (distributionEmbedding original - distributionEmbedding zeroth -
        ∑ coordinate : Fin 2, distributionDerivative coordinate (distributionEmbedding (flux coordinate))) := by
  rw [startupDivDivRemainder, negativeResolvent_distribution, map_sub, map_sum, l2ToNegative_distribution, map_sub]
  simp only [derivativeToNegative_distribution, map_sub]

/-- The genuine distributional divergence-form equation becomes the exact
fixed-point equation for the SAME rough field and the actual tensor resolvent.
The principal map has the negative sign required by (1-Delta)^-1. -/
theorem startupSameField_divDiv_resolvent (kernels : TensorIndex → FieldL2 →L[ℂ] FieldL2)
    (original zeroth : FieldL2) (flux : Fin 2 → FieldL2)
    (equation : Laplacian.laplacian (distributionEmbedding original) =
      (∑ index : TensorIndex,
        distributionDerivative index.1 (distributionDerivative index.2 (distributionEmbedding (kernels index original)))) +
      distributionEmbedding zeroth +
      ∑ coordinate : Fin 2, distributionDerivative coordinate (distributionEmbedding (flux coordinate))) :
    original + startupSecondKernelSumFor kernels original =
      valueInclusion (startupDivDivRemainder original zeroth flux) := by
  apply distributionEmbedding_injective
  rw [map_add, startupSecondKernelSumFor_distribution, startupDivDivRemainder_distribution]
  have recovered := distributionResolvent_left (distributionEmbedding original)
  rw [equation] at recovered
  have rearranged : distributionEmbedding original -
      ((∑ index : TensorIndex,
        distributionDerivative index.1 (distributionDerivative index.2 (distributionEmbedding (kernels index original)))) +
        distributionEmbedding zeroth +
        ∑ coordinate : Fin 2, distributionDerivative coordinate (distributionEmbedding (flux coordinate))) =
      (distributionEmbedding original - distributionEmbedding zeroth -
        ∑ coordinate : Fin 2, distributionDerivative coordinate (distributionEmbedding (flux coordinate))) -
      ∑ index : TensorIndex,
        distributionDerivative index.1 (distributionDerivative index.2 (distributionEmbedding (kernels index original))) := by
    abel
  rw [rearranged, map_sub] at recovered
  exact (sub_eq_iff_eq_add.mp recovered).symm

end Grad.CartesianStartup
