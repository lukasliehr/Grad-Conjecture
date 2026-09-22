import AKCC5FixedTensorFiniteKernelFormula

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000

open MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.RepresentedKernel Grad.RepresentedKernel.SpatialProduct Grad.RepresentedKernel.WeakDerivatives

theorem startupKernel_zero_of_coefficient {Parameter : Type*} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure] {input output : ℕ}
    (data : Grad.FullCellKernel.L2KernelData measure input output openUnitDisk)
    (zero : ∀ outer inner pair, data.coefficient outer inner pair = 0) : Grad.FullCellKernel.kernel data = 0 := by
  have entries (outer inner : ℤ) : Grad.FullCellKernel.entry data outer inner = 0 := by
    apply ContinuousLinearMap.ext
    intro field
    apply Lp.ext
    filter_upwards [startup_entry_ae data outer inner field,
      Lp.coeFn_zero (PhysicalValue output) 2 (volume.restrict openUnitDisk)] with point same zeroValue
    rw [same]
    simp only [zero, zero_apply, integral_zero, zeroValue, Pi.zero_apply]
  apply ContinuousLinearMap.ext
  intro field
  apply (Grad.FullCellKernel.coordinateIsometry output openUnitDisk).injective
  apply lp.ext
  funext cell
  rw [Grad.FullCellKernel.coordinateIsometry_apply, Grad.FullCellKernel.coordinateIsometry_apply,
    Grad.FullCellKernel.kernel_coordinate]
  simp only [entries, zero_apply, tsum_zero, map_zero]

theorem startupFixed_positiveAllocation_zero {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    {input output : ℕ}
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue input output)
    (measurable : Measurable coefficient) (integrable : Integrable coefficient measure)
    {rank : ℕ} (word : DerivativeIndex rank) (selected : Finset (Fin rank))
    (nonempty : selected.Nonempty) (target : Word selectedᶜ.card) :
    operator (allocatedData (startupFixedRawData measure orthogonal invariant actionMeasurable coefficient measurable integrable)
      word selected target) (0, 0) 0 = 0 := by
  apply startupKernel_zero_of_coefficient
  intro outer inner pair
  change Grad.CellWeights.derivativeFactor 0 (outer - inner) •
    coefficientDerivative (0, 0)
      ((allocatedData (startupFixedRawData measure orthogonal invariant actionMeasurable coefficient measurable integrable)
        word selected target).coefficient outer inner) pair = 0
  rw [coefficientDerivative_zero]
  have nonzero : selectedIndex word selected ≠ (0, 0) := by
    intro equal
    have total := allocationIndices rank word selected
    rw [equal] at total
    have positive := Finset.card_pos.mpr nonempty
    omega
  change Grad.CellWeights.derivativeFactor 0 (outer - inner) •
    ((chainProduct (startupFixedRawData measure orthogonal invariant actionMeasurable coefficient measurable integrable)
      word selected target pair.1 : ℂ) •
      coefficientDerivative (selectedIndex word selected)
        (fun pair => if outer = inner then coefficient pair.1 else 0) pair) = 0
  rw [startupParameterDerivative (fun parameter => if outer = inner then coefficient parameter else 0), if_neg nonzero]
  apply ContinuousLinearMap.ext
  intro value
  simp only [smul_apply, zero_apply, smul_zero]

end Grad.CartesianStartup
