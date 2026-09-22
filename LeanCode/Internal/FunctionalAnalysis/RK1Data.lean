import FullCellKernelProof
import CB1Scalar
import WTCInterface

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open scoped BigOperators ContDiff Topology

namespace Grad.RepresentedKernel

def coefficientDerivative {Parameter : Type*} {inputDimension outputDimension : ℕ}
    (multiindex : ℕ × ℕ)
    (coefficient : Parameter × Spatial →
      PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension)
    (pair : Parameter × Spatial) :
    PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension :=
  iteratedFDeriv ℝ (multiindex.1 + multiindex.2)
    (fun point => coefficient (pair.1, point)) pair.2
    (fun position => spatialDirection
      (Grad.WeakTesting.Commutation.canonicalWord multiindex.1 multiindex.2 position))

theorem coefficientDerivative_zero {Parameter : Type*} {inputDimension outputDimension : ℕ}
    (coefficient : Parameter × Spatial →
      PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension) :
    coefficientDerivative (0, 0) coefficient = coefficient := by
  rfl

structure RawKernelData {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) (inputDimension outputDimension : ℕ)
    (domain : Set Spatial) where
  domainOpen : IsOpen domain
  orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial
  invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant domain (orthogonal parameter)
  actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2)
  coefficient : ℤ → ℤ → Parameter × Spatial →
    PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension
  coefficientSmooth : ∀ output input parameter,
    ContDiffOn ℝ ∞ (fun point => coefficient output input (parameter, point)) domain
  derivativeMeasurable : ∀ multiindex output input,
    AEStronglyMeasurable (coefficientDerivative multiindex (coefficient output input))
      (measure.prod (volume.restrict domain))
  envelope : ℤ → ℤ → Spatial → ℝ
  envelopeOneLe : ∀ output input, ∀ᵐ pair ∂measure.prod (volume.restrict domain),
    1 ≤ envelope output input pair.2
  majorant : (ℕ × ℕ) → ℕ → ℤ → ℤ → Parameter → ℝ
  majorantMeasurable : ∀ multiindex moment output input,
    Measurable (majorant multiindex moment output input)
  majorantNonnegative : ∀ multiindex moment output input parameter,
    0 ≤ majorant multiindex moment output input parameter
  majorantIntegrable : ∀ multiindex moment output input,
    Integrable (majorant multiindex moment output input) measure
  domination : ∀ multiindex moment output input,
    ∀ᵐ pair ∂measure.prod (volume.restrict domain),
    ‖coefficientDerivative multiindex (coefficient output input) pair‖ *
        Grad.CellWeights.cellWeight (output - input) ^ moment *
        envelope output input pair.2 ≤ majorant multiindex moment output input pair.1
  rowBound : (ℕ × ℕ) → ℕ → ℝ
  columnBound : (ℕ × ℕ) → ℕ → ℝ
  rowNonnegative : ∀ multiindex moment, 0 ≤ rowBound multiindex moment
  columnNonnegative : ∀ multiindex moment, 0 ≤ columnBound multiindex moment
  rowsSummable : ∀ multiindex moment output,
    Summable (fun input : ℤ => ∫ parameter,
      majorant multiindex moment output input parameter ∂measure)
  columnsSummable : ∀ multiindex moment input,
    Summable (fun output : ℤ => ∫ parameter,
      majorant multiindex moment output input parameter ∂measure)
  rows : ∀ multiindex moment output,
    (∑' input : ℤ, ∫ parameter, majorant multiindex moment output input parameter ∂measure) ≤
      rowBound multiindex moment
  columns : ∀ multiindex moment input,
    (∑' output : ℤ, ∫ parameter, majorant multiindex moment output input parameter ∂measure) ≤
      columnBound multiindex moment

variable {Parameter : Type*} [MeasurableSpace Parameter]
  {measure : Measure Parameter} {inputDimension outputDimension : ℕ} {domain : Set Spatial}
  (data : RawKernelData measure inputDimension outputDimension domain)

def momentCoefficient (multiindex : ℕ × ℕ) (moment : ℕ) (output input : ℤ)
    (pair : Parameter × Spatial) :
    PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension :=
  Grad.CellWeights.derivativeFactor moment (output - input) •
    coefficientDerivative multiindex (data.coefficient output input) pair

theorem momentCoefficient_zero (output input : ℤ) :
    momentCoefficient data (0, 0) 0 output input = data.coefficient output input := by
  funext pair
  simp only [momentCoefficient, Grad.CellWeights.derivativeFactor, pow_zero, one_smul,
    coefficientDerivative_zero]

theorem momentCoefficient_apply (multiindex : ℕ × ℕ) (moment : ℕ) (output input : ℤ)
    (pair : Parameter × Spatial) (value : PhysicalValue inputDimension) :
    momentCoefficient data multiindex moment output input pair value =
      Grad.CellWeights.derivativeFactor moment (output - input) •
        coefficientDerivative multiindex (data.coefficient output input) pair value := rfl

end Grad.RepresentedKernel
