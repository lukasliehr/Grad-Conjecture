import CE1Proof
import SK2Proof
import KI1ProofConsumer
import CPGProof

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue FieldL2 fieldCellProjection cellSingle)
open scoped BigOperators Topology

namespace Grad.FullCellKernel

abbrev CoordinateFields (dimension : ℕ) (domain : Set Spatial) :=
  lp (fun _ : ℤ => Lp (PhysicalValue dimension) 2 (volume.restrict domain)) 2

def insertCell (dimension : ℕ) (domain : Set Spatial) (cell : ℤ) :
    Lp (PhysicalValue dimension) 2 (volume.restrict domain) →L[ℂ] FieldL2 dimension domain :=
  (cellSingle (PhysicalValue dimension) cell).compLpL 2 (volume.restrict domain)

def ExchangeGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial),
    ∃ exchange : FieldL2 dimension domain ≃ₗᵢ[ℂ] CoordinateFields dimension domain,
      ∀ (field : FieldL2 dimension domain) (cell : ℤ),
        exchange field cell = fieldCellProjection dimension domain cell field

structure L2KernelData {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) (inputDimension outputDimension : ℕ) (domain : Set Spatial) where
  domainMeasurable : MeasurableSet domain
  orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial
  invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant domain (orthogonal parameter)
  actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2)
  coefficient : ℤ → ℤ → Parameter × Spatial →
    PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension
  weight : ℤ → ℤ → Parameter → ℝ
  coefficientMeasurable : ∀ output input,
    AEStronglyMeasurable (coefficient output input) (measure.prod (volume.restrict domain))
  weightMeasurable : ∀ output input, Measurable (weight output input)
  weightNonnegative : ∀ output input parameter, 0 ≤ weight output input parameter
  weightIntegrable : ∀ output input, Integrable (weight output input) measure
  domination : ∀ output input, ∀ᵐ pair ∂measure.prod (volume.restrict domain),
    ‖coefficient output input pair‖ ≤ weight output input pair.1
  rowBound : ℝ
  columnBound : ℝ
  rowNonnegative : 0 ≤ rowBound
  columnNonnegative : 0 ≤ columnBound
  rowsSummable : ∀ output, Summable (fun input : ℤ => ∫ parameter, weight output input parameter ∂measure)
  columnsSummable : ∀ input, Summable (fun output : ℤ => ∫ parameter, weight output input parameter ∂measure)
  rows : ∀ output, (∑' input : ℤ, ∫ parameter, weight output input parameter ∂measure) ≤ rowBound
  columns : ∀ input, (∑' output : ℤ, ∫ parameter, weight output input parameter ∂measure) ≤ columnBound

def entry {Parameter : Type*} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : L2KernelData measure inputDimension outputDimension domain) (output input : ℤ) :
    Lp (PhysicalValue inputDimension) 2 (volume.restrict domain) →L[ℂ]
      Lp (PhysicalValue outputDimension) 2 (volume.restrict domain) :=
  Grad.KernelIntegral.integralKernelCLM measure data.domainMeasurable data.orthogonal
    data.invariant data.actionMeasurable (data.coefficient output input) (data.weight output input)
    (data.coefficientMeasurable output input) (data.weightMeasurable output input)
    (data.weightNonnegative output input) (data.weightIntegrable output input) (data.domination output input)

def KernelSpec {Parameter : Type*} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : L2KernelData measure inputDimension outputDimension domain)
    (kernel : FieldL2 inputDimension domain →L[ℂ] FieldL2 outputDimension domain) : Prop :=
  ‖kernel‖ ≤ Real.sqrt (data.rowBound * data.columnBound) ∧
  (∀ (field : FieldL2 inputDimension domain) (output : ℤ),
    fieldCellProjection outputDimension domain output (kernel field) =
      ∑' input : ℤ, entry data output input (fieldCellProjection inputDimension domain input field)) ∧
  (∀ (field : FieldL2 inputDimension domain) (cells : Finset ℤ),
    (∀ input ∉ cells, fieldCellProjection inputDimension domain input field = 0) →
    ∀ᵐ point ∂volume.restrict domain, ∀ output : ℤ,
      kernel field point output = ∑ input ∈ cells,
        ∫ parameter, data.coefficient output input (parameter, point)
          (field (data.orthogonal parameter point) input) ∂measure) ∧
  (∀ field : FieldL2 inputDimension domain,
    Filter.Tendsto (fun cells : Finset ℤ =>
      Grad.CellProjections.Generic.fieldProjection (volume.restrict domain)
        (PhysicalValue outputDimension) cells
          (kernel (Grad.CellProjections.Generic.fieldProjection (volume.restrict domain)
            (PhysicalValue inputDimension) cells field))) Filter.atTop (𝓝 (kernel field)))

def KernelGoal : Prop :=
  ∀ (Parameter : Type*) [MeasurableSpace Parameter] (measure : Measure Parameter) [SigmaFinite measure]
    (inputDimension outputDimension : ℕ) (domain : Set Spatial)
    (data : L2KernelData measure inputDimension outputDimension domain),
    ∃ kernel : FieldL2 inputDimension domain →L[ℂ] FieldL2 outputDimension domain,
      KernelSpec data kernel

#check LinearIsometryEquiv.ofSurjective
#check AntilipschitzWith.isClosed_range
#check lp.hasSum_single
#check ContinuousLinearMap.coeFn_compLpL
#check Grad.CellEnergy.field_norm_sq_eq_tsum
#check Grad.SchurKernel.Discrete.discreteActionCLM
#check Grad.CellProjections.Generic.rectangular_sections

end Grad.FullCellKernel
