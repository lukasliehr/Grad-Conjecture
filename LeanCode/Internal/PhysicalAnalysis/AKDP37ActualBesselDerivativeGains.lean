import AKDM4SecondTensorRemainderAbsorption

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.TensorBootstrap Grad.SobolevBridge

/-- The same Bessel resolvent commutes with a distribution derivative. -/
theorem startupDistributionResolvent_derivative (direction : Fin 2) (field : FieldDistribution) :
    distributionResolvent (distributionDerivative direction field) =
      distributionDerivative direction (distributionResolvent field) := by
  rw [distributionDerivative_eq_multiplier,distributionDerivative_eq_multiplier]
  change TemperedDistribution.fourierMultiplierCLM CellValues inverseBesselSymbol
    (TemperedDistribution.fourierMultiplierCLM CellValues (firstDerivativeSymbol direction) field) =
    TemperedDistribution.fourierMultiplierCLM CellValues (firstDerivativeSymbol direction)
      (TemperedDistribution.fourierMultiplierCLM CellValues inverseBesselSymbol field)
  rw [distributionMultiplier_comp inverseBesselSymbol_temperate (firstDerivativeSymbol_temperate direction),
    distributionMultiplier_comp (firstDerivativeSymbol_temperate direction) inverseBesselSymbol_temperate,
    mul_comm inverseBesselSymbol]

theorem startupFirstResolvent_distribution (direction : Fin 2) (field : FieldL2) :
    distributionEmbedding (l2ResolventDerivative direction field) =
      distributionResolvent (distributionDerivative direction (distributionEmbedding field)) := by
  rw [l2ResolventDerivative_distribution,l2Resolvent_distribution,startupDistributionResolvent_derivative]

/-- The actual negative-resolvent value is exactly the L2 Bessel formula. -/
theorem startupDivDivRemainder_value (original zeroth : FieldL2) (flux : Fin 2 → FieldL2) :
    valueInclusion (startupDivDivRemainder original zeroth flux) =
      l2Resolvent original-l2Resolvent zeroth-∑ direction : Fin 2,l2ResolventDerivative direction (flux direction) := by
  apply distributionEmbedding_injective
  simp only [startupDivDivRemainder_distribution,map_sub,map_sum,l2Resolvent_distribution,
    startupFirstResolvent_distribution]

/-- Shift two actual derivatives from the zeroth field into the bounded
second Bessel multiplier, retaining the same represented derivative. -/
theorem startupResolvent_actualSecond (index : TensorIndex) (field derivative : FieldL2)
    (same : distributionEmbedding derivative=
      distributionDerivative index.1 (distributionDerivative index.2 (distributionEmbedding field))) :
    l2Resolvent derivative=startupSecondL2 index field := by
  apply distributionEmbedding_injective
  rw [l2Resolvent_distribution,same,startupSecondL2_distribution]

/-- One derivative on a flux combines with its divergence resolvent. -/
theorem startupFluxResolvent_actualFirst (direction coordinate : Fin 2) (field derivative : FieldL2)
    (same : distributionEmbedding derivative=distributionDerivative coordinate (distributionEmbedding field)) :
    l2ResolventDerivative direction derivative=startupSecondL2 (direction,coordinate) field := by
  apply distributionEmbedding_injective
  rw [startupFirstResolvent_distribution,same,startupSecondL2_distribution]

/-- Exact lower-representative Bessel bound. In the application original
and zeroth use rank-2 and flux uses rank-1; no H1 norm is paid. -/
theorem startupDivDivRemainder_lower_norm (index : TensorIndex)
    (original zeroth : FieldL2) (flux : Fin 2 → FieldL2)
    (originalLower zeroLower : FieldL2) (fluxLower : Fin 2 → FieldL2)
    (originalSame : distributionEmbedding original=
      distributionDerivative index.1 (distributionDerivative index.2 (distributionEmbedding originalLower)))
    (zeroSame : distributionEmbedding zeroth=
      distributionDerivative index.1 (distributionDerivative index.2 (distributionEmbedding zeroLower)))
    (fluxSame : ∀ direction,distributionEmbedding (flux direction)=
      distributionDerivative index.2 (distributionEmbedding (fluxLower direction))) :
    ‖valueInclusion (startupDivDivRemainder original zeroth flux)‖ ≤
      ‖originalLower‖+‖zeroLower‖+∑ direction : Fin 2,‖fluxLower direction‖ := by
  rw [startupDivDivRemainder_value,startupResolvent_actualSecond index originalLower original originalSame,
    startupResolvent_actualSecond index zeroLower zeroth zeroSame]
  simp_rw [startupFluxResolvent_actualFirst _ index.2 _ _ (fluxSame _)]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) (norm_sum_le _ _)).trans
  apply add_le_add
  · exact add_le_add
      (startupSecondL2_norm index originalLower)
      (startupSecondL2_norm index zeroLower)
  · apply Finset.sum_le_sum
    intro direction _
    exact startupSecondL2_norm (direction,index.2) (fluxLower direction)

end Grad.CartesianStartup
