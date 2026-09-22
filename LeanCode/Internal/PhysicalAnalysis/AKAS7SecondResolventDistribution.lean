import AKAS5ExactSecondResolvent

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.TensorBootstrap

/-- The actual tensor insertion has precisely one distribution entry. -/
theorem startupTensorSingle_distribution (index coordinate : TensorIndex) (field : FieldL2) :
    distributionEmbedding (startupTensorSingle index field coordinate) =
      if index = coordinate then distributionEmbedding field else 0 := by
  classical
  change distributionEmbedding
    (PiLp.single (β := fun _ : TensorIndex => FieldL2) 2 index field coordinate) = _
  by_cases same : index = coordinate
  · subst coordinate
    simp only [PiLp.single_eq_same, if_true]
  · simp only [PiLp.single_eq_of_ne' 2 same, if_neg same, map_zero]

theorem startupDistributionDivDiv_single (index : TensorIndex) (distribution : FieldDistribution) :
    distributionDivDiv (fun coordinate => if index = coordinate then distribution else 0) =
      distributionDerivative index.1 (distributionDerivative index.2 distribution) := by
  classical
  simp [distributionDivDiv, apply_ite, map_zero]

/-- Literal Bessel resolvent of the chosen distributional second derivative. -/
theorem startupSecondL2_distribution (index : TensorIndex) (field : FieldL2) :
    distributionEmbedding (startupSecondL2 index field) =
      distributionResolvent
        (distributionDerivative index.1 (distributionDerivative index.2 (distributionEmbedding field))) := by
  change distributionEmbedding (tensorL2Resolvent (startupTensorSingle index field)) = _
  rw [tensorL2Resolvent_distribution]
  simp_rw [startupTensorSingle_distribution]
  rw [startupDistributionDivDiv_single]

end Grad.CartesianStartup
