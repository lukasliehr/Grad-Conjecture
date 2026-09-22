import AKCC22OriginalFixedAllOrderGraphs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.WeightedJets Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

theorem startupOrderedDerivative_unique {dimension order rank weight : ℕ}
    (field : GraphGrade dimension order weight openUnitDisk) (bound : rank ≤ order)
    (derivatives : Tensor rank (StartupL2 dimension))
    (weak : ∀ word, HasWeakOrderedDerivative dimension openUnitDisk rank word
      (base dimension order openUnitDisk (fun _ => weight) field) (derivatives word)) :
    orderedDerivative dimension order rank openUnitDisk (fun _ => weight) bound field = derivatives := by
  apply PiLp.ext
  intro word
  exact Grad.WeakTesting.Commutation.weakEquality dimension openUnitDisk openUnitDisk_isOpen rank word word
    (fun _ => rfl) _ _ _ (orderedDerivative_hasWeak dimension order rank openUnitDisk (fun _ => weight) bound field word)
    (weak word)

variable {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    {input output : ℕ}
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue input output)
    (measurable : Measurable coefficient) (integrable : Integrable coefficient measure)

theorem startupFixedTensor_exactSplit {order rank weight : ℕ}
    (liftMeasurable : Measurable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)))
    (liftIntegrable : Integrable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)) measure)
    (field : GraphGrade input order weight openUnitDisk) (bound : rank ≤ order)
    (leading remainder : Tensor rank (StartupL2 input))
    (weak : ∀ word, HasWeakOrderedDerivative input openUnitDisk rank word
      (base input order openUnitDisk (fun _ => weight) field) ((leading + remainder) word)) (word : DerivativeIndex rank) :
    HasWeakOrderedDerivative output openUnitDisk rank word
      (Grad.FullCellKernel.kernel (startupFixedKernelData measure orthogonal invariant actionMeasurable coefficient measurable integrable)
        (base input order openUnitDisk (fun _ => weight) field))
      ((startupFixedTensorKernel measure rank orthogonal invariant actionMeasurable coefficient liftMeasurable liftIntegrable leading +
        startupFixedTensorKernel measure rank orthogonal invariant actionMeasurable coefficient liftMeasurable liftIntegrable remainder) word) := by
  have actual := startupFixedTensor_orderedWeak measure orthogonal invariant actionMeasurable coefficient measurable integrable
    liftMeasurable liftIntegrable word bound field
  rw [startupOrderedDerivative_unique field bound (leading + remainder) weak, map_add] at actual
  exact actual

end Grad.CartesianStartup
