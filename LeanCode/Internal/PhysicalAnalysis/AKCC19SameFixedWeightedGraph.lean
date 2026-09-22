import AKCC18FixedKernelCellWeightCommutation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2400
open MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.WeightedJets Grad.WeightedJets.Ordered

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

/-- The cell weight stays inside the complete graph coordinates. The fixed
angular kernel acts on the literal SAME underlying field and preserves any
cell weight, independently of the spatial order. -/
def startupFixedWeightedGraph {order weight : ℕ}
    (field : GraphGrade input order weight openUnitDisk) : GraphGrade output order weight openUnitDisk :=
  startupGraphRestoreWeight weight
    (startupFixedGraph measure orthogonal invariant actionMeasurable coefficient measurable integrable
      liftMeasurable liftIntegrable (startupGraphRemoveWeight field))

theorem startupFixedWeightedGraph_base {order weight : ℕ}
    (field : GraphGrade input order weight openUnitDisk) :
    base output order openUnitDisk (fun _ => weight)
      (startupFixedWeightedGraph measure orthogonal invariant actionMeasurable coefficient measurable integrable liftMeasurable liftIntegrable field) =
    Grad.FullCellKernel.kernel (startupFixedKernelData measure orthogonal invariant actionMeasurable coefficient measurable integrable)
      (base input order openUnitDisk (fun _ => weight) field) := by
  unfold startupFixedWeightedGraph
  rw [startupGraphRestoreWeight_base, startupFixedGraph_base, startupGraphRemoveWeight_base,
    ← startupFixed_inverseWeight, base_apply]

end Grad.CartesianStartup
