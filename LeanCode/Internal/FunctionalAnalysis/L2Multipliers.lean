import BesselResolvent
import Mathlib.Analysis.Fourier.LpSpace

noncomputable section

open MeasureTheory FourierTransform

namespace Grad.PDEBootstrap

abbrev BoundedSymbol := Lp ℂ ⊤ (volume : Measure Spatial)

def symbolAction (symbol : BoundedSymbol) : FieldL2 →L[ℂ] FieldL2 :=
  LinearMap.mkContinuous
    { toFun := fun field => symbol • field
      map_add' := fun first second => Lp.add_smul symbol first second
      map_smul' := fun scalar field => by
        exact (Lp.smul_comm scalar symbol field).symm }
    ‖symbol‖ (fun field => Lp.norm_smul_le symbol field)

def l2Multiplier (symbol : BoundedSymbol) : FieldL2 →L[ℂ] FieldL2 :=
  (Lp.fourierTransformₗᵢ Spatial CellValues).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    symbolAction symbol ∘L
      (Lp.fourierTransformₗᵢ Spatial CellValues).toContinuousLinearEquiv.toContinuousLinearMap

theorem l2Multiplier_apply (symbol : BoundedSymbol) (field : FieldL2) :
    l2Multiplier symbol field = 𝓕⁻ (symbol • 𝓕 field : FieldL2) := rfl

theorem l2Multiplier_norm_le (symbol : BoundedSymbol) (field : FieldL2) :
    ‖l2Multiplier symbol field‖ ≤ ‖symbol‖ * ‖field‖ := by
  change ‖(Lp.fourierTransformₗᵢ Spatial CellValues).symm (symbol • 𝓕 field : FieldL2)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (Lp.norm_smul_le symbol (𝓕 field : FieldL2)).trans_eq
    (congrArg (fun size => ‖symbol‖ * size) (Lp.norm_fourier_eq field))

theorem l2Multiplier_opNorm_le (symbol : BoundedSymbol) : ‖l2Multiplier symbol‖ ≤ ‖symbol‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (l2Multiplier_norm_le symbol)

theorem l2Multiplier_distribution {symbol : Spatial → ℂ}
    (growth : symbol.HasTemperateGrowth) (bounded : MemLp symbol ⊤ (volume : Measure Spatial))
    (field : FieldL2) :
    distributionEmbedding (l2Multiplier (bounded.toLp symbol) field) =
      TemperedDistribution.fourierMultiplierCLM CellValues symbol (distributionEmbedding field) := by
  change Lp.toTemperedDistribution (𝓕⁻ (bounded.toLp symbol • 𝓕 field : FieldL2)) =
    𝓕⁻ (TemperedDistribution.smulLeftCLM CellValues symbol (𝓕 (Lp.toTemperedDistribution field)))
  rw [← Lp.fourierInv_toTemperedDistribution_eq,
    Lp.toTemperedDistribution_smul_eq growth bounded, ← Lp.fourier_toTemperedDistribution_eq]

theorem inverseBesselSymbol_norm_le (frequency : Spatial) : ‖inverseBesselSymbol frequency‖ ≤ 1 := by
  simp only [inverseBesselSymbol, Complex.norm_real, Real.norm_eq_abs, abs_inv,
    abs_of_pos (besselWeight_pos frequency)]
  exact inv_le_one_of_one_le₀ (besselWeight_one_le frequency)

theorem inverseBesselSymbol_memLp : MemLp inverseBesselSymbol ⊤ (volume : Measure Spatial) :=
  ⟨inverseBesselSymbol_temperate.1.continuous.aestronglyMeasurable,
    eLpNormEssSup_lt_top_of_ae_bound (Filter.Eventually.of_forall inverseBesselSymbol_norm_le)⟩

theorem symbol_linf_norm_le_one {symbol : Spatial → ℂ}
    (bounded : MemLp symbol ⊤ (volume : Measure Spatial))
    (pointwiseBound : ∀ frequency, ‖symbol frequency‖ ≤ 1) : ‖bounded.toLp symbol‖ ≤ 1 := by
  rw [Lp.norm_toLp]
  have seminormBound : eLpNorm symbol ⊤ (volume : Measure Spatial) ≤ 1 := by
    simpa only [ENNReal.ofReal_one, eLpNorm_exponent_top] using
      eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall pointwiseBound)
  simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono (by simp) seminormBound

theorem inverseBesselSymbol_linf_norm_le :
    ‖inverseBesselSymbol_memLp.toLp inverseBesselSymbol‖ ≤ 1 :=
  symbol_linf_norm_le_one inverseBesselSymbol_memLp inverseBesselSymbol_norm_le

def l2Resolvent : FieldL2 →L[ℂ] FieldL2 :=
  l2Multiplier (inverseBesselSymbol_memLp.toLp inverseBesselSymbol)

theorem l2Resolvent_norm_le (field : FieldL2) : ‖l2Resolvent field‖ ≤ ‖field‖ := by
  exact (l2Multiplier_norm_le _ field).trans
    (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right inverseBesselSymbol_linf_norm_le (norm_nonneg field))

theorem l2Resolvent_opNorm_le : ‖l2Resolvent‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro field
  simpa only [one_mul] using l2Resolvent_norm_le field

theorem l2Resolvent_distribution (field : FieldL2) :
    distributionEmbedding (l2Resolvent field) = distributionResolvent (distributionEmbedding field) :=
  l2Multiplier_distribution inverseBesselSymbol_temperate inverseBesselSymbol_memLp field

theorem l2Resolvent_equation (field : FieldL2) :
    distributionEmbedding (l2Resolvent field) -
      Laplacian.laplacian (distributionEmbedding (l2Resolvent field)) = distributionEmbedding field := by
  rw [l2Resolvent_distribution]
  exact distributionResolvent_right _

theorem l2Resolvent_unique (source solution : FieldL2)
    (equation : distributionEmbedding solution - Laplacian.laplacian (distributionEmbedding solution) =
      distributionEmbedding source) : l2Resolvent source = solution := by
  apply distributionEmbedding_injective
  rw [l2Resolvent_distribution, ← equation]
  exact distributionResolvent_left _

end Grad.PDEBootstrap
