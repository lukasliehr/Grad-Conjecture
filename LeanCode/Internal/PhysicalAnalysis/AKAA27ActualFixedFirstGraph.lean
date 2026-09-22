import AKAA26RawFirstGraphBounds

noncomputable section

set_option maxHeartbeats 1600000

open MeasureTheory Classical
open scoped BigOperators ContDiff Topology

namespace Grad.CartesianStartup

open Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.RepresentedKernel Grad.RepresentedKernel.SpatialProduct

variable {Parameter : Type*} [MeasurableSpace Parameter]

theorem startupFirstAllocation_sum (value : ℝ) :
    (∑ selected : Finset (Fin 1), ∑ _target : Word selectedᶜ.card, value) = 3 * value := by
  have enumeration : (Finset.univ : Finset (Finset (Fin 1))) = {∅, Finset.univ} := by decide
  rw [enumeration, Finset.sum_pair (by decide : (∅ : Finset (Fin 1)) ≠ Finset.univ)]
  change (∑ _ : Fin 1 → Fin 2, value) + (∑ _ : Fin 0 → Fin 2, value) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    pow_one, pow_zero, nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_one, one_mul]
  ring

def startupFixedFirstGraph (measure : Measure Parameter) [SigmaFinite measure]
    {inputDimension outputDimension : ℕ}
    (orthogonal : Parameter → Grad.PDEBootstrap.Spatial ≃ₗᵢ[ℝ] Grad.PDEBootstrap.Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (measurable : Measurable (fun pair : Parameter × Grad.PDEBootstrap.Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue inputDimension outputDimension)
    (coefficientMeasurable : Measurable coefficient) (integrable : Integrable coefficient measure) :
    GraphGrade inputDimension 1 0 openUnitDisk →L[ℂ] GraphGrade outputDimension 1 0 openUnitDisk :=
  startupRawFirstGraphCLM (startupFixedRawData measure orthogonal invariant measurable coefficient coefficientMeasurable integrable)

theorem startupFixedFirstGraph_base (measure : Measure Parameter) [SigmaFinite measure]
    {inputDimension outputDimension : ℕ}
    (orthogonal : Parameter → Grad.PDEBootstrap.Spatial ≃ₗᵢ[ℝ] Grad.PDEBootstrap.Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (measurable : Measurable (fun pair : Parameter × Grad.PDEBootstrap.Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue inputDimension outputDimension)
    (coefficientMeasurable : Measurable coefficient) (integrable : Integrable coefficient measure)
    (field : GraphGrade inputDimension 1 0 openUnitDisk) :
    base outputDimension 1 openUnitDisk (fun _ => 0)
        (startupFixedFirstGraph measure orthogonal invariant measurable coefficient coefficientMeasurable integrable field) =
      Grad.FullCellKernel.kernel (startupFixedKernelData measure orthogonal invariant measurable coefficient coefficientMeasurable integrable)
        (base inputDimension 1 openUnitDisk (fun _ => 0) field) := by
  change base outputDimension 1 openUnitDisk (fun _ => 0) (startupRawFirstGraph _ field) = _
  rw [startupRawFirstGraph_base, startupFixedRawData_operator]

theorem startupFixedFirstGraph_budget (measure : Measure Parameter) [SigmaFinite measure]
    {inputDimension outputDimension : ℕ}
    (orthogonal : Parameter → Grad.PDEBootstrap.Spatial ≃ₗᵢ[ℝ] Grad.PDEBootstrap.Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (measurable : Measurable (fun pair : Parameter × Grad.PDEBootstrap.Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue inputDimension outputDimension)
    (coefficientMeasurable : Measurable coefficient) (integrable : Integrable coefficient measure) :
    startupRawFirstBudget (startupFixedRawData measure orthogonal invariant measurable coefficient coefficientMeasurable integrable) =
      7 * ∫ parameter, ‖coefficient parameter‖ ∂measure := by
  let integral := ∫ parameter, ‖coefficient parameter‖ ∂measure
  change Real.sqrt (integral * integral) +
    (∑ selected : Finset (Fin 1), ∑ _target : Word selectedᶜ.card, Real.sqrt (integral * integral)) +
    (∑ selected : Finset (Fin 1), ∑ _target : Word selectedᶜ.card, Real.sqrt (integral * integral)) = 7 * integral
  rw [Real.sqrt_mul_self (integral_nonneg (fun _ => norm_nonneg _)), startupFirstAllocation_sum]
  ring

theorem startupFixedFirstGraph_norm (measure : Measure Parameter) [SigmaFinite measure]
    {inputDimension outputDimension : ℕ}
    (orthogonal : Parameter → Grad.PDEBootstrap.Spatial ≃ₗᵢ[ℝ] Grad.PDEBootstrap.Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (measurable : Measurable (fun pair : Parameter × Grad.PDEBootstrap.Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue inputDimension outputDimension)
    (coefficientMeasurable : Measurable coefficient) (integrable : Integrable coefficient measure) :
    ‖startupFixedFirstGraph measure orthogonal invariant measurable coefficient coefficientMeasurable integrable‖ ≤
      7 * ∫ parameter, ‖coefficient parameter‖ ∂measure := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) (integral_nonneg (fun _ => norm_nonneg _)))
  intro field
  exact (startupRawFirstGraph_bound _ field).trans_eq
    (congrArg (fun bound : ℝ => bound * ‖field‖)
      (startupFixedFirstGraph_budget measure orthogonal invariant measurable coefficient coefficientMeasurable integrable))

end Grad.CartesianStartup
