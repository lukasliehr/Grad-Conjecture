import AKCC9FixedKernelOrderedWeak

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000

open MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.RepresentedKernel Grad.RepresentedKernel.SpatialProduct Grad.RepresentedKernel.WeakDerivatives
open Grad.WeightedJets Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

theorem startupFixed_derivativeCandidate {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    {input output order rank weight : ℕ}
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue input output)
    (measurable : Measurable coefficient) (integrable : Integrable coefficient measure)
    (word : DerivativeIndex rank) (bound : rank ≤ order)
    (field : GraphGrade input order weight openUnitDisk) :
    (∑ selected : Finset (Fin rank), ∑ target : Word selectedᶜ.card,
      operator (allocatedData (startupFixedRawData measure orthogonal invariant actionMeasurable coefficient measurable integrable)
        word selected target) (0, 0) 0
        (inputDerivative input order rank weight openUnitDisk bound field selected target)) =
      ∑ target : DerivativeIndex rank,
        startupFixedChainKernel measure orthogonal invariant actionMeasurable coefficient measurable integrable rank word target
          (orderedDerivative input order rank openUnitDisk (fun _ => weight) bound field target) := by
  rw [Finset.sum_eq_single (∅ : Finset (Fin rank))]
  · apply Fintype.sum_equiv (startupFullWordEquiv rank).symm
    intro source
    obtain ⟨target, rfl⟩ := (startupFullWordEquiv rank).surjective source
    rw [Equiv.symm_apply_apply, startupEmpty_inputDerivative]
    exact congrArg (fun kernel : StartupL2 input →L[ℂ] StartupL2 output =>
      kernel (orderedDerivative input order rank openUnitDisk (fun _ => weight) bound field target))
      (startupFixed_emptyAllocation_operator measure orthogonal invariant actionMeasurable coefficient measurable integrable rank word target)
  · intro selected _ different
    apply Finset.sum_eq_zero
    intro target _
    rw [startupFixed_positiveAllocation_zero measure orthogonal invariant actionMeasurable coefficient measurable integrable
      word selected (Finset.nonempty_iff_ne_empty.mpr different) target, zero_apply]
  · simp

/-- Exact arbitrary-order weak covariance of the SAME fixed full-cell kernel.
The derivative is the literal ordered covector lift whose norm is independent
of rank in BW. No smoothness of the input beyond its given graph is assumed. -/
theorem startupFixedTensor_orderedWeak {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    {input output order rank weight : ℕ}
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue input output)
    (measurable : Measurable coefficient) (integrable : Integrable coefficient measure)
    (liftMeasurable : Measurable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)))
    (liftIntegrable : Integrable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)) measure)
    (word : DerivativeIndex rank) (bound : rank ≤ order)
    (field : GraphGrade input order weight openUnitDisk) :
    HasWeakOrderedDerivative output openUnitDisk rank word
      (Grad.FullCellKernel.kernel (startupFixedKernelData measure orthogonal invariant actionMeasurable coefficient measurable integrable)
        (base input order openUnitDisk (fun _ => weight) field))
      (startupFixedTensorKernel measure rank orthogonal invariant actionMeasurable coefficient liftMeasurable liftIntegrable
        (orderedDerivative input order rank openUnitDisk (fun _ => weight) bound field) word) := by
  have weak := startupFixed_orderedWeak_allocated measure orthogonal invariant actionMeasurable coefficient measurable integrable word bound field
  rw [startupFixed_derivativeCandidate measure orthogonal invariant actionMeasurable coefficient measurable integrable word bound field] at weak
  rw [startupFixedTensor_coordinate measure orthogonal invariant actionMeasurable coefficient measurable integrable rank liftMeasurable liftIntegrable]
  exact weak

end Grad.CartesianStartup
