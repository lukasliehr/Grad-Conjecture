import GraphIdentification

noncomputable section

namespace Grad.SobolevBridge

open Grad.PDEBootstrap

def negativeResolvent : Sobolev (-1) ≃ₗᵢ[ℂ] FieldH1 :=
  sobolevResolvent.trans sobolevOneEquivGraph

theorem negativeResolvent_distribution (source : Sobolev (-1)) :
    distributionEmbedding (valueInclusion (negativeResolvent source)) =
      distributionResolvent (sobolevDistribution (-1) source) := by
  change distributionEmbedding (valueInclusion (sobolevOneEquivGraph (sobolevResolvent source))) = _
  rw [sobolevOneEquivGraph_distribution, sobolevResolvent_distribution]

theorem negativeResolvent_norm (source : Sobolev (-1)) : ‖negativeResolvent source‖ = ‖source‖ :=
  negativeResolvent.norm_map source

def negativeResolventCLM : Sobolev (-1) →L[ℂ] FieldH1 :=
  negativeResolvent.toLinearIsometry.toContinuousLinearMap

theorem negativeResolventCLM_opNorm_le : ‖negativeResolventCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro source
  change ‖negativeResolvent source‖ ≤ 1 * ‖source‖
  rw [negativeResolvent_norm, one_mul]

theorem negativeResolvent_equation (source : Sobolev (-1)) :
    distributionEmbedding (valueInclusion (negativeResolvent source)) -
      Laplacian.laplacian (distributionEmbedding (valueInclusion (negativeResolvent source))) =
        sobolevDistribution (-1) source := by
  rw [negativeResolvent_distribution]
  exact distributionResolvent_right _

theorem negativeResolvent_unique (source : Sobolev (-1)) (solution : FieldH1)
    (equation : distributionEmbedding (valueInclusion solution) -
      Laplacian.laplacian (distributionEmbedding (valueInclusion solution)) =
        sobolevDistribution (-1) source) : negativeResolvent source = solution := by
  apply valueInclusion_injective
  apply distributionEmbedding_injective
  rw [negativeResolvent_distribution, ← equation]
  exact distributionResolvent_left _

theorem halfL2_norm_le (field : FieldL2) : ‖halfL2 field‖ ≤ ‖field‖ := by
  have bound := symbol_linf_norm_le_one halfSymbol_memLp halfSymbol_norm_le
  have scaled := mul_le_mul_of_nonneg_right bound (norm_nonneg field)
  exact (l2Multiplier_norm_le _ field).trans
    (by simpa only [one_mul] using scaled)

theorem firstHalfL2_norm_le (coordinate : Fin 2) (field : FieldL2) :
    ‖firstHalfL2 coordinate field‖ ≤ ‖field‖ := by
  have bound := symbol_linf_norm_le_one (firstHalfSymbol_memLp coordinate) (firstHalfSymbol_norm_le coordinate)
  have scaled := mul_le_mul_of_nonneg_right bound (norm_nonneg field)
  exact (l2Multiplier_norm_le _ field).trans
    (by simpa only [one_mul] using scaled)

def l2ToNegative : FieldL2 →L[ℂ] Sobolev (-1) :=
  (sobolevCoordinates (-1)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L halfL2

theorem l2ToNegative_distribution (field : FieldL2) :
    sobolevDistribution (-1) (l2ToNegative field) = distributionEmbedding field := by
  apply distributionWeight_injective (-1 / 2)
  rw [sobolevDistribution_recover]
  exact halfL2_distribution field

theorem l2ToNegative_norm_le (field : FieldL2) : ‖l2ToNegative field‖ ≤ ‖field‖ := by
  change ‖(sobolevCoordinates (-1)).symm (halfL2 field)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact halfL2_norm_le field

def derivativeToNegative (coordinate : Fin 2) : FieldL2 →L[ℂ] Sobolev (-1) :=
  (sobolevCoordinates (-1)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L firstHalfL2 coordinate

theorem derivativeToNegative_distribution (coordinate : Fin 2) (field : FieldL2) :
    sobolevDistribution (-1) (derivativeToNegative coordinate field) =
      distributionDerivative coordinate (distributionEmbedding field) := by
  apply distributionWeight_injective (-1 / 2)
  rw [sobolevDistribution_recover]
  change distributionEmbedding (firstHalfL2 coordinate field) = _
  rw [firstHalfL2_distribution, distributionDerivative_eq_multiplier]
  change TemperedDistribution.fourierMultiplierCLM CellValues (firstHalfSymbol coordinate)
    (distributionEmbedding field) =
      TemperedDistribution.fourierMultiplierCLM CellValues halfSymbol
        (TemperedDistribution.fourierMultiplierCLM CellValues (firstDerivativeSymbol coordinate)
          (distributionEmbedding field))
  rw [distributionMultiplier_comp halfSymbol_temperate (firstDerivativeSymbol_temperate coordinate),
    firstHalfSymbol, mul_comm halfSymbol]

theorem derivativeToNegative_norm_le (coordinate : Fin 2) (field : FieldL2) :
    ‖derivativeToNegative coordinate field‖ ≤ ‖field‖ := by
  change ‖(sobolevCoordinates (-1)).symm (firstHalfL2 coordinate field)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact firstHalfL2_norm_le coordinate field

abbrev FluxL2 := PiLp 2 (fun _ : Fin 2 => FieldL2)

def divergenceToNegative : FluxL2 →L[ℂ] Sobolev (-1) :=
  ∑ coordinate : Fin 2, derivativeToNegative coordinate ∘L PiLp.proj 2 (fun _ : Fin 2 => FieldL2) coordinate

theorem divergenceToNegative_apply (flux : FluxL2) :
    divergenceToNegative flux = ∑ coordinate : Fin 2, derivativeToNegative coordinate (flux coordinate) := by
  simp [divergenceToNegative]

theorem divergenceToNegative_distribution (flux : FluxL2) :
    sobolevDistribution (-1) (divergenceToNegative flux) =
      ∑ coordinate : Fin 2, distributionDerivative coordinate (distributionEmbedding (flux coordinate)) := by
  rw [divergenceToNegative_apply, map_sum]
  simp_rw [derivativeToNegative_distribution]

theorem divergenceToNegative_norm_le (flux : FluxL2) : ‖divergenceToNegative flux‖ ≤ 2 * ‖flux‖ := by
  rw [divergenceToNegative_apply]
  calc
    _ ≤ ∑ coordinate : Fin 2, ‖derivativeToNegative coordinate (flux coordinate)‖ := norm_sum_le _ _
    _ ≤ ∑ _coordinate : Fin 2, ‖flux‖ := Finset.sum_le_sum (fun coordinate _ =>
      (derivativeToNegative_norm_le coordinate (flux coordinate)).trans (PiLp.norm_apply_le flux coordinate))
    _ = _ := by simp

theorem negativeDistribution_decomposition (source : Sobolev (-1)) :
    sobolevDistribution (-1) source = distributionEmbedding (halfL2 source.coordinate) -
      ∑ coordinate : Fin 2, distributionDerivative coordinate
        (distributionEmbedding (firstHalfL2 coordinate source.coordinate)) := by
  change distributionWeight (-(-1) / 2) (distributionEmbedding source.coordinate) = _
  rw [neg_neg, distribution_half_reconstruction, ← halfL2_distribution]
  congr 1
  apply Finset.sum_congr rfl
  intro coordinate membership
  rw [firstHalfL2_distribution, distributionDerivative_eq_multiplier,
    distributionDerivative_eq_multiplier,
    distributionMultiplier_comp (firstHalfSymbol_temperate coordinate) (firstDerivativeSymbol_temperate coordinate),
    distributionMultiplier_comp (firstDerivativeSymbol_temperate coordinate) (firstHalfSymbol_temperate coordinate),
    mul_comm]

theorem negative_range_iff_l2_divergence (field : FieldDistribution) :
    field ∈ Set.range (sobolevDistribution (-1)) ↔
      ∃ zeroth : FieldL2, ∃ flux : FluxL2,
        distributionEmbedding zeroth +
          (∑ coordinate : Fin 2, distributionDerivative coordinate (distributionEmbedding (flux coordinate))) =
            field := by
  constructor
  · rintro ⟨source, rfl⟩
    refine ⟨halfL2 source.coordinate, WithLp.toLp 2 (fun coordinate => -firstHalfL2 coordinate source.coordinate), ?_⟩
    change distributionEmbedding (halfL2 source.coordinate) +
      (∑ coordinate : Fin 2, distributionDerivative coordinate
        (distributionEmbedding (-firstHalfL2 coordinate source.coordinate))) = _
    simp_rw [map_neg, Finset.sum_neg_distrib, ← sub_eq_add_neg]
    exact (negativeDistribution_decomposition source).symm
  · rintro ⟨zeroth, flux, equality⟩
    refine ⟨l2ToNegative zeroth + divergenceToNegative flux, ?_⟩
    rw [map_add, l2ToNegative_distribution, divergenceToNegative_distribution]
    exact equality

theorem negativeResolvent_l2_compatible (source : FieldL2) :
    negativeResolvent (l2ToNegative source) = h1Resolvent source := by
  apply valueInclusion_injective
  apply distributionEmbedding_injective
  rw [negativeResolvent_distribution, l2ToNegative_distribution, h1Resolvent_value, l2Resolvent_distribution]

def roughResolventRemainder (zeroth : FieldL2) (flux : FluxL2) (remainder : Sobolev (-1)) : FieldH1 :=
  negativeResolvent (l2ToNegative zeroth + divergenceToNegative flux - remainder)

theorem roughResolventRemainder_distribution (zeroth : FieldL2) (flux : FluxL2)
    (remainder : Sobolev (-1)) :
    distributionEmbedding (valueInclusion (roughResolventRemainder zeroth flux remainder)) =
      distributionResolvent (distributionEmbedding zeroth +
        (∑ coordinate : Fin 2, distributionDerivative coordinate (distributionEmbedding (flux coordinate))) -
          sobolevDistribution (-1) remainder) := by
  rw [roughResolventRemainder, negativeResolvent_distribution, map_sub, map_add,
    l2ToNegative_distribution, divergenceToNegative_distribution]

theorem roughResolventRemainder_norm_le (zeroth : FieldL2) (flux : FluxL2)
    (remainder : Sobolev (-1)) :
    ‖roughResolventRemainder zeroth flux remainder‖ ≤ ‖zeroth‖ + 2 * ‖flux‖ + ‖remainder‖ := by
  rw [roughResolventRemainder, negativeResolvent_norm]
  calc
    _ ≤ ‖l2ToNegative zeroth + divergenceToNegative flux‖ + ‖remainder‖ := norm_sub_le _ _
    _ ≤ (‖l2ToNegative zeroth‖ + ‖divergenceToNegative flux‖) + ‖remainder‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add (l2ToNegative_norm_le zeroth) (divergenceToNegative_norm_le flux)) le_rfl

end Grad.SobolevBridge
