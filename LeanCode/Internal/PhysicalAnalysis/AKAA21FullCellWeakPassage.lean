import AKAA20LiteralFirstWeakProduct

noncomputable section

set_option maxHeartbeats 1400000

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators ContDiff Topology

namespace Grad.CartesianStartup

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.RepresentedKernel
open Grad.RepresentedKernel.WeakDerivatives Grad.RepresentedKernel.SpatialProduct
open Grad.WeakTesting Grad.WeakTesting.Commutation

theorem startupKernel_row_hasSum {Parameter : Type*} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension : ℕ} {domain : Set Grad.PDEBootstrap.Spatial}
    (data : Grad.FullCellKernel.L2KernelData measure inputDimension outputDimension domain)
    (field : FieldL2 inputDimension domain) (output : ℤ) :
    HasSum (fun input : ℤ => Grad.FullCellKernel.entry data output input
      (fieldCellProjection inputDimension domain input field))
      (fieldCellProjection outputDimension domain output (Grad.FullCellKernel.kernel data field)) := by
  have summable := Grad.SchurKernel.Discrete.row_summable
    (Grad.FullCellKernel.entry data) (Grad.FullCellKernel.integratedWeight data)
    (Grad.FullCellKernel.integratedWeight_nonneg data) (Grad.FullCellKernel.entry_norm_le data)
    data.rowsSummable (Grad.FullCellKernel.coordinateIsometry inputDimension domain field) output
  rw [Grad.FullCellKernel.kernel_coordinate]
  exact summable.hasSum

theorem startupWeak_hasSum {Index : Type*} {dimension rank : ℕ}
    {domain : Set Grad.PDEBootstrap.Spatial} (word : Word rank)
    (fields derivatives : Index → FieldL2 dimension domain) (field derivative : FieldL2 dimension domain)
    (fieldsSum : HasSum fields field) (derivativesSum : HasSum derivatives derivative)
    (weak : ∀ index, HasWeakOrderedDerivative dimension domain rank word (fields index) (derivatives index)) :
    HasWeakOrderedDerivative dimension domain rank word field derivative := by
  intro cell vector test smooth compact supported
  have left := (compactPairing dimension domain cell vector test smooth compact).hasSum derivativesSum
  have right := (signedDerivativePairing dimension domain cell vector test smooth compact rank word).hasSum fieldsSum
  have equality : (fun index => compactPairing dimension domain cell vector test smooth compact (derivatives index)) =
      (fun index => signedDerivativePairing dimension domain cell vector test smooth compact rank word (fields index)) := by
    funext index
    exact weak index cell vector test smooth compact supported
  rw [equality] at left
  exact left.unique right

theorem startupPairing_projection_eq {dimension : ℕ} {domain : Set Grad.PDEBootstrap.Spatial}
    (cell : ℤ) (vector : PhysicalValue dimension) (test : Grad.PDEBootstrap.Spatial → ℝ)
    (membership : MemLp test 2 (volume.restrict domain)) (first second : FieldL2 dimension domain)
    (same : fieldCellProjection dimension domain cell first = fieldCellProjection dimension domain cell second) :
    pairingOfMemLp dimension domain cell vector test membership first =
      pairingOfMemLp dimension domain cell vector test membership second := by
  rw [pairingOfMemLp_apply, pairingOfMemLp_apply]
  apply integral_congr_ae
  filter_upwards [fieldCellProjection_ae dimension domain first,
    fieldCellProjection_ae dimension domain second] with point firstCoordinate secondCoordinate
  have coordinate := congrArg (fun field : Lp (PhysicalValue dimension) 2 (volume.restrict domain) => field point) same
  rw [firstCoordinate cell, secondCoordinate cell] at coordinate
  rw [coordinate]

theorem startupWeak_from_rows {dimension rank : ℕ} {domain : Set Grad.PDEBootstrap.Spatial}
    (word : Word rank) (field derivative : FieldL2 dimension domain)
    (weak : ∀ cell : ℤ, HasWeakOrderedDerivative dimension domain rank word
      (Grad.FullCellKernel.insertCell dimension domain cell (fieldCellProjection dimension domain cell field))
      (Grad.FullCellKernel.insertCell dimension domain cell (fieldCellProjection dimension domain cell derivative))) :
    HasWeakOrderedDerivative dimension domain rank word field derivative := by
  intro cell vector test smooth compact supported
  have equation := weak cell cell vector test smooth compact supported
  have fieldSame : fieldCellProjection dimension domain cell
      (Grad.FullCellKernel.insertCell dimension domain cell (fieldCellProjection dimension domain cell field)) =
      fieldCellProjection dimension domain cell field := by
    rw [Grad.FullCellKernel.projection_insertCell, if_pos rfl]
  have derivativeSame : fieldCellProjection dimension domain cell
      (Grad.FullCellKernel.insertCell dimension domain cell (fieldCellProjection dimension domain cell derivative)) =
      fieldCellProjection dimension domain cell derivative := by
    rw [Grad.FullCellKernel.projection_insertCell, if_pos rfl]
  change pairingOfMemLp dimension domain cell vector test _ _ =
    (-1 : ℂ) ^ rank • pairingOfMemLp dimension domain cell vector (orderedTestDerivative rank word test) _ _ at equation
  rw [startupPairing_projection_eq cell vector test _ _ derivative derivativeSame,
    startupPairing_projection_eq cell vector (orderedTestDerivative rank word test) _ _ field fieldSame] at equation
  exact equation

end Grad.CartesianStartup
