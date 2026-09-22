import AKCC17ConstantWeightGraphCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Physical.RadialLedger

variable {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    {input output : ℕ}
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue input output)
    (measurable : Measurable coefficient) (integrable : Integrable coefficient measure)

theorem startupFixed_inverseWeight (weight : ℕ) (field : StartupL2 input) :
    Grad.FullCellKernel.kernel (startupFixedKernelData measure orthogonal invariant actionMeasurable coefficient measurable integrable)
      (Grad.CellWeights.inverseFieldCLM input openUnitDisk weight field) =
      Grad.CellWeights.inverseFieldCLM output openUnitDisk weight
        (Grad.FullCellKernel.kernel (startupFixedKernelData measure orthogonal invariant actionMeasurable coefficient measurable integrable) field) := by
  apply Lp.ext
  filter_upwards [startupFixed_representative measure orthogonal invariant actionMeasurable coefficient measurable integrable
      (Grad.CellWeights.inverseFieldCLM input openUnitDisk weight field)
      (fun point cell => Grad.CellWeights.inverseFactor weight cell • field point cell)
      (Grad.CellWeights.inverseFieldCLM_coordinate input openUnitDisk weight field),
    Grad.CellWeights.inverseFieldCLM_coordinate output openUnitDisk weight
      (Grad.FullCellKernel.kernel (startupFixedKernelData measure orthogonal invariant actionMeasurable coefficient measurable integrable) field),
    startupFixed_coordinate_ae measure orthogonal invariant actionMeasurable coefficient measurable integrable field]
      with point transformed inverse original
  apply lp.ext
  funext cell
  rw [transformed cell, inverse cell, original cell]
  simp only [map_smul]
  exact integral_smul _ _

end Grad.CartesianStartup
