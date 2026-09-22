import AKCC7EmptyOrderedAllocation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

open MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.RepresentedKernel Grad.RepresentedKernel.SpatialProduct Grad.RepresentedKernel.WeakDerivatives

theorem startupChainFactor_cast {first second : ℕ} (same : first = second)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (word target : DerivativeIndex second) :
    chainFactor first orthogonal (fun position => word (Fin.cast same position))
      (fun position => target (Fin.cast same position)) = chainFactor second orthogonal word target := by
  cases same
  rfl

theorem startupFixed_emptyAllocation_operator {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    {input output : ℕ}
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue input output)
    (measurable : Measurable coefficient) (integrable : Integrable coefficient measure)
    (rank : ℕ) (word target : DerivativeIndex rank) :
    operator (allocatedData (startupFixedRawData measure orthogonal invariant actionMeasurable coefficient measurable integrable)
      word ∅ (fun position => target (Fin.cast (startupEmpty_complement_card rank) position))) (0, 0) 0 =
      startupFixedChainKernel measure orthogonal invariant actionMeasurable coefficient measurable integrable rank word target := by
  unfold operator startupFixedChainKernel
  refine startupKernel_congr _ _ ?_ ?_
  · rfl
  intro outer inner
  filter_upwards [] with pair
  rw [l2Data_zero_coefficient]
  change (chainProduct (startupFixedRawData measure orthogonal invariant actionMeasurable coefficient measurable integrable)
      word ∅ (fun position => target (Fin.cast (startupEmpty_complement_card rank) position)) pair.1 : ℂ) •
      coefficientDerivative (selectedIndex word ∅)
        (fun pair => if outer = inner then coefficient pair.1 else 0) pair =
      if outer = inner then startupFixedChainCoefficient orthogonal coefficient rank word target pair.1 else 0
  rw [startupEmpty_selectedIndex, coefficientDerivative_zero, chainProduct, startupFull_subword, startupChainFactor_cast]
  by_cases same : outer = inner
  · simp only [if_pos same]
    rfl
  · simp only [if_neg same]
    apply ContinuousLinearMap.ext
    intro value
    simp only [smul_apply, zero_apply, smul_zero]

end Grad.CartesianStartup
