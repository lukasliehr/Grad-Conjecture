import AKCC15OrderedWeakGraphAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2300

open MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.WeightedJets Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

variable {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    {input output : ℕ}
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue input output)
    (measurable : Measurable coefficient) (integrable : Integrable coefficient measure)
    (liftMeasurable : ∀ rank, Measurable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)))
    (liftIntegrable : ∀ rank, Integrable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)) measure)

def startupFixedGraph {order weight : ℕ} (field : GraphGrade input order weight openUnitDisk) : GraphGrade output order 0 openUnitDisk := by
  let original := Grad.FullCellKernel.kernel (startupFixedKernelData measure orthogonal invariant actionMeasurable coefficient measurable integrable)
    (base input order openUnitDisk (fun _ => weight) field)
  let derivatives := fun index : JetIndex order =>
    startupFixedTensorKernel measure (degree index) orthogonal invariant actionMeasurable coefficient
      (liftMeasurable (degree index)) (liftIntegrable (degree index))
      (orderedDerivative input order (degree index) openUnitDisk (fun _ => weight) index.property field) (derivativeWord index)
  have weak (index : JetIndex order) :
      HasWeakOrderedDerivative output openUnitDisk (degree index) (derivativeWord index) original (derivatives index) :=
    startupFixedTensor_orderedWeak measure orthogonal invariant actionMeasurable coefficient measurable integrable
      (liftMeasurable (degree index)) (liftIntegrable (degree index)) (derivativeWord index) index.property field
  have zero : derivatives (zeroIndex order) = original :=
    (Grad.WeakTesting.Commutation.zero output openUnitDisk openUnitDisk_isOpen (derivativeWord (zeroIndex order))
      original (derivatives (zeroIndex order))).mp (weak (zeroIndex order))
  exact startupGraphFromWeak original derivatives zero weak

theorem startupFixedGraph_base {order weight : ℕ} (field : GraphGrade input order weight openUnitDisk) :
    base output order openUnitDisk (fun _ => 0)
      (startupFixedGraph measure orthogonal invariant actionMeasurable coefficient measurable integrable liftMeasurable liftIntegrable field) =
    Grad.FullCellKernel.kernel (startupFixedKernelData measure orthogonal invariant actionMeasurable coefficient measurable integrable)
      (base input order openUnitDisk (fun _ => weight) field) :=
by
  unfold startupFixedGraph
  apply startupGraphFromWeak_base

end Grad.CartesianStartup
