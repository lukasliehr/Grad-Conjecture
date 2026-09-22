import AKBW8FixedCovectorCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.CartesianStartup
open MeasureTheory Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.Ledger

private theorem coefficient_expansion {input output : ℕ} (coefficient : OperatorValue input output) :
    coefficient = ∑ column : Fin input, columnEmbedding input output column (coefficient (operatorBasis column)) := by
  apply ContinuousLinearMap.ext
  intro vector
  rw [← operatorBasis_expansion vector, map_sum]
  rw [operatorBasis_expansion]
  simp only [sum_apply, columnEmbedding_apply, map_smul]

private theorem coefficient_continuous_of_values {Parameter : Type*} [TopologicalSpace Parameter]
    {input output : ℕ} (coefficient : Parameter → OperatorValue input output)
    (continuousValues : ∀ vector, Continuous (fun parameter => coefficient parameter vector)) : Continuous coefficient := by
  have same : coefficient = fun parameter => ∑ column : Fin input,
      columnEmbedding input output column (coefficient parameter (operatorBasis column)) :=
    funext (fun parameter => coefficient_expansion (coefficient parameter))
  rw [same]
  exact continuous_finsetSum _ (fun column _ =>
    (columnEmbedding input output column).continuous.comp (continuousValues (operatorBasis column)))

theorem startupCovectorCoefficient_continuous {Parameter : Type*} [TopologicalSpace Parameter]
    {input output : ℕ} (rank : ℕ)
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (actionContinuous : Continuous (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue input output) (coefficientContinuous : Continuous coefficient) :
    Continuous (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)) := by
  apply coefficient_continuous_of_values
  intro vector
  let tensor := (startupTensorValueEquiv input rank).symm vector
  have componentContinuous (word : DerivativeIndex rank) :
      Continuous (fun parameter => coefficient parameter
        (∑ source : DerivativeIndex rank,
          ((∏ position : Fin rank,
            orthogonal parameter (spatialDirection (word position)) (source position) : ℝ) : ℂ) • tensor source)) := by
    apply coefficientContinuous.clm_apply
    apply continuous_finsetSum
    intro source _
    have scalarContinuous : Continuous (fun parameter =>
        ((∏ position : Fin rank,
          orthogonal parameter (spatialDirection (word position)) (source position) : ℝ) : ℂ)) := by
      apply Complex.continuous_ofReal.comp
      apply continuous_finsetProd
      intro position _
      exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) (source position)).comp
        (actionContinuous.comp (continuous_id.prodMk continuous_const))
    exact scalarContinuous.smul (continuous_const (y := tensor source))
  have tupleContinuous := (PiLp.continuous_toLp 2 (fun _ : DerivativeIndex rank => PhysicalValue output)).comp
    (continuous_pi componentContinuous)
  have result := (startupTensorValueEquiv output rank).continuous.comp tupleContinuous
  apply result.congr
  intro parameter
  apply (startupTensorValueEquiv output rank).symm.injective
  simp only [Function.comp_apply, LinearIsometryEquiv.symm_apply_apply]
  apply PiLp.ext
  intro word
  have same := startupCovectorCoefficient_apply rank (orthogonal parameter) (coefficient parameter) tensor word
  simpa only [tensor, LinearIsometryEquiv.apply_symm_apply] using same.symm

theorem startupCovectorCoefficient_integrable {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) {input output : ℕ} (rank : ℕ)
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (coefficient : Parameter → OperatorValue input output) (integrable : Integrable coefficient measure)
    (measurable : AEStronglyMeasurable
      (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)) measure) :
    Integrable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)) measure :=
  integrable.norm.mono' measurable (Filter.Eventually.of_forall
    (fun parameter => startupCovectorCoefficient_norm rank (orthogonal parameter) (coefficient parameter)))

end Grad.CartesianStartup
