import AKCC4TensorFixedLiteralAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 2200

open MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.RepresentedKernel.SpatialProduct

variable {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    {input output : ℕ}
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue input output)
    (measurable : Measurable coefficient) (integrable : Integrable coefficient measure)

def startupFixedChainKernel (rank : ℕ) (word target : DerivativeIndex rank) : StartupL2 input →L[ℂ] StartupL2 output :=
  Grad.FullCellKernel.kernel (startupFixedKernelData measure orthogonal invariant actionMeasurable
    (startupFixedChainCoefficient orthogonal coefficient rank word target)
    (startupFixedChainCoefficient_measurable measure orthogonal invariant actionMeasurable coefficient measurable integrable rank word target)
    (startupFixedChainCoefficient_integrable measure orthogonal invariant actionMeasurable coefficient measurable integrable rank word target))

theorem startupFixedTensor_coordinate (rank : ℕ)
    (liftMeasurable : Measurable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)))
    (liftIntegrable : Integrable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)) measure)
    (fields : Tensor rank (StartupL2 input)) (word : DerivativeIndex rank) :
    startupFixedTensorKernel measure rank orthogonal invariant actionMeasurable coefficient liftMeasurable liftIntegrable fields word =
      ∑ target : DerivativeIndex rank,
        startupFixedChainKernel measure orthogonal invariant actionMeasurable coefficient measurable integrable rank word target (fields target) := by
  let summand := fun target : DerivativeIndex rank =>
    startupFixedChainKernel measure orthogonal invariant actionMeasurable coefficient measurable integrable rank word target (fields target)
  have rows : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ target : DerivativeIndex rank, ∀ cell : ℤ,
      Integrable (fun parameter => startupFixedChainCoefficient orthogonal coefficient rank word target parameter
        (fields target (orthogonal parameter point) cell)) measure := by
    apply ae_all_iff.mpr
    intro target
    exact startupFixed_rows_integrable measure orthogonal invariant actionMeasurable
      (startupFixedChainCoefficient orthogonal coefficient rank word target)
      (startupFixedChainCoefficient_measurable measure orthogonal invariant actionMeasurable coefficient measurable integrable rank word target)
      (startupFixedChainCoefficient_integrable measure orthogonal invariant actionMeasurable coefficient measurable integrable rank word target) (fields target)
  have action : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ target : DerivativeIndex rank, ∀ cell : ℤ,
      summand target point cell = ∫ parameter, startupFixedChainCoefficient orthogonal coefficient rank word target parameter
        (fields target (orthogonal parameter point) cell) ∂measure := by
    apply ae_all_iff.mpr
    intro target
    exact startupFixed_coordinate_ae measure orthogonal invariant actionMeasurable
      (startupFixedChainCoefficient orthogonal coefficient rank word target)
      (startupFixedChainCoefficient_measurable measure orthogonal invariant actionMeasurable coefficient measurable integrable rank word target)
      (startupFixedChainCoefficient_integrable measure orthogonal invariant actionMeasurable coefficient measurable integrable rank word target) (fields target)
  apply Lp.ext
  filter_upwards [startupFixedTensor_coordinate_ae measure rank orthogonal invariant actionMeasurable coefficient liftMeasurable liftIntegrable fields,
    rows, action, Lp.coeFn_fun_finsetSum Finset.univ summand] with point tensor row terms sumValues
  apply lp.ext
  funext cell
  change _ = (∑ target, summand target) point cell
  rw [tensor cell word, sumValues]
  change _ = (∑ target, summand target point) cell
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, terms]
  rw [← integral_finsetSum _ (fun target _ => row target cell)]
  apply integral_congr_ae
  filter_upwards [] with parameter
  simp only [startupFixedChainCoefficient, smul_apply, map_sum, map_smul]

end Grad.CartesianStartup
