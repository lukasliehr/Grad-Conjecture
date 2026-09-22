import CM1Consumer
import CK2Consumer
import SP1Consumers

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open Grad.RepresentedKernel.SpatialProduct
open scoped BigOperators ContDiff Topology

universe outerUniverse innerUniverse

namespace Grad.RepresentedKernel.Composition.Spatial

abbrev Parameter (Outer : Type*) (Inner : Type*) := ℤ × (Outer × Inner)

abbrev parameterMeasure {Outer Inner : Type*} [MeasurableSpace Outer] [MeasurableSpace Inner]
    (outerMeasure : Measure Outer) (innerMeasure : Measure Inner) : Measure (Parameter Outer Inner) :=
  (Measure.count : Measure ℤ).prod (outerMeasure.prod innerMeasure)

def canonicalWord (multiindex : ℕ × ℕ) : Word (multiindex.1 + multiindex.2) :=
  Grad.WeakTesting.Commutation.canonicalWord multiindex.1 multiindex.2

def wordIndex {rank : ℕ} (word : Word rank) : ℕ × ℕ :=
  (Grad.WeakTesting.Commutation.directionCount word 0,
    Grad.WeakTesting.Commutation.directionCount word 1)

def outerIndex (multiindex : ℕ × ℕ) (selected : Finset (Fin (multiindex.1 + multiindex.2))) : ℕ × ℕ :=
  wordIndex (subword (canonicalWord multiindex) selected)

def unitEnvelope : ℤ → ℤ → Spatial → ℝ := fun _ _ _ => 1

def unitData {Parameter : Type*} [MeasurableSpace Parameter] {measure : Measure Parameter}
    {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain) :
    RawKernelData measure inputDimension outputDimension domain :=
  { data with
    envelope := unitEnvelope
    envelopeOneLe := fun _ _ => Filter.Eventually.of_forall (fun _ => le_refl 1)
    domination := fun multiindex moment output input => by
      simpa only [unitEnvelope, mul_one] using derivative_domination data multiindex moment output input }

def spatialBound (outerBound innerBound : (ℕ × ℕ) → ℕ → ℝ) (multiindex : ℕ × ℕ) (moment : ℕ) : ℝ :=
  ∑ selected : Finset (Fin (multiindex.1 + multiindex.2)), ∑ target : Word (selectedᶜ).card,
    Moments.allocatedBound moment (outerBound (outerIndex multiindex selected)) (innerBound (wordIndex target))

variable {Outer : Type outerUniverse} {Inner : Type innerUniverse}
  [MeasurableSpace Outer] [MeasurableSpace Inner]
  {outerMeasure : Measure Outer} {innerMeasure : Measure Inner}
  {inputDimension middleDimension outputDimension : ℕ} {domain : Set Spatial}
  (outer : RawKernelData outerMeasure middleDimension outputDimension domain)
  (inner : RawKernelData innerMeasure inputDimension middleDimension domain)

def coefficient (output input : ℤ) (pair : Parameter Outer Inner × Spatial) :
    PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension :=
  composedCoefficient outer.orthogonal outer.coefficient inner.coefficient output input pair.1 pair.2

def derivativeTerm (multiindex : ℕ × ℕ) (selected : Finset (Fin (multiindex.1 + multiindex.2)))
    (target : Word (selectedᶜ).card) (output input : ℤ) (pair : Parameter Outer Inner × Spatial) :
    PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension :=
  chainFactor (selectedᶜ).card (outer.orthogonal pair.1.2.1)
    (subword (canonicalWord multiindex) selectedᶜ) target •
      Moments.derivativePairCoefficient outer inner (outerIndex multiindex selected) (wordIndex target)
        output input pair

def majorant (multiindex : ℕ × ℕ) (moment : ℕ) (output input : ℤ) (parameter : Parameter Outer Inner) : ℝ :=
  ∑ selected : Finset (Fin (multiindex.1 + multiindex.2)), ∑ target : Word (selectedᶜ).card,
    Moments.parameterMajorant outer inner (outerIndex multiindex selected) (wordIndex target)
      moment output input parameter

def integratedMajorant (multiindex : ℕ × ℕ) (moment : ℕ) (output input : ℤ) : ℝ :=
  ∑ selected : Finset (Fin (multiindex.1 + multiindex.2)), ∑ target : Word (selectedᶜ).card,
    Moments.allocatedWeight moment
      (fun allocation => Grad.FullCellKernel.integratedWeight (l2Data outer (outerIndex multiindex selected) allocation))
      (fun allocation => Grad.FullCellKernel.integratedWeight (l2Data inner (wordIndex target) allocation)) output input

def DataSpecification (envelope : ℤ → ℤ → Spatial → ℝ)
    (data : RawKernelData (parameterMeasure outerMeasure innerMeasure) inputDimension outputDimension domain) : Prop :=
  data.coefficient = coefficient outer inner ∧
    data.orthogonal = composedOrthogonal outer.orthogonal inner.orthogonal ∧
    data.envelope = envelope ∧
    data.majorant = majorant outer inner ∧
    data.rowBound = spatialBound outer.rowBound inner.rowBound ∧
    data.columnBound = spatialBound outer.columnBound inner.columnBound

def AllocationGoal : Prop :=
  ∀ (multiindex : ℕ × ℕ) (selected : Finset (Fin (multiindex.1 + multiindex.2)))
    (target : Word (selectedᶜ).card),
    (outerIndex multiindex selected).1 + (outerIndex multiindex selected).2 +
      (wordIndex target).1 + (wordIndex target).2 = multiindex.1 + multiindex.2 ∧
    ∀ moment allocation : ℕ, allocation ≤ moment →
      ((outerIndex multiindex selected).1 + (outerIndex multiindex selected).2 + allocation) +
        ((wordIndex target).1 + (wordIndex target).2 + (moment - allocation)) =
          multiindex.1 + multiindex.2 + moment

def ChainFactorGoal : Prop :=
  ∀ (rank : ℕ) (word target : Word rank),
    Measurable (fun parameter => chainFactor rank (outer.orthogonal parameter) word target) ∧
      ∀ parameter, |chainFactor rank (outer.orthogonal parameter) word target| ≤ 1

def DerivativeGoal : Prop :=
  (∀ output input parameter, ContDiffOn ℝ ∞
    (fun point => coefficient outer inner output input (parameter, point)) domain) ∧
  ∀ (multiindex : ℕ × ℕ) (output input : ℤ) (pair : Parameter Outer Inner × Spatial), pair.2 ∈ domain →
    coefficientDerivative multiindex (coefficient outer inner output input) pair =
      ∑ selected : Finset (Fin (multiindex.1 + multiindex.2)), ∑ target : Word (selectedᶜ).card,
        derivativeTerm outer inner multiindex selected target output input pair

def DerivativeMeasurableGoal : Prop :=
  ∀ multiindex output input,
    AEStronglyMeasurable (coefficientDerivative multiindex (coefficient outer inner output input))
      ((parameterMeasure outerMeasure innerMeasure).prod (volume.restrict domain))

def UnitDataGoal : Prop :=
  (unitData outer).envelope = unitEnvelope ∧
    (unitData outer).coefficient = outer.coefficient ∧
    (unitData outer).orthogonal = outer.orthogonal ∧
    (unitData outer).majorant = outer.majorant ∧
    (unitData outer).rowBound = outer.rowBound ∧
    (unitData outer).columnBound = outer.columnBound ∧
    ∀ multiindex moment, l2Data (unitData outer) multiindex moment = l2Data outer multiindex moment

def MajorantGoal : Prop :=
  ∀ multiindex moment,
    (∀ output input,
      (∀ parameter, majorant outer inner multiindex moment output input parameter =
        ∑ selected : Finset (Fin (multiindex.1 + multiindex.2)), ∑ target : Word (selectedᶜ).card,
          ∑ allocation ∈ Finset.range (moment + 1), (moment.choose allocation : ℝ) *
            (outer.majorant (outerIndex multiindex selected) allocation output parameter.1 parameter.2.1 *
              inner.majorant (wordIndex target) (moment - allocation) parameter.1 input parameter.2.2)) ∧
      Measurable (majorant outer inner multiindex moment output input) ∧
      (∀ parameter, 0 ≤ majorant outer inner multiindex moment output input parameter) ∧
      Integrable (majorant outer inner multiindex moment output input) (parameterMeasure outerMeasure innerMeasure) ∧
      (∫ parameter, majorant outer inner multiindex moment output input parameter
        ∂parameterMeasure outerMeasure innerMeasure) = integratedMajorant outer inner multiindex moment output input) ∧
    0 ≤ spatialBound outer.rowBound inner.rowBound multiindex moment ∧
    0 ≤ spatialBound outer.columnBound inner.columnBound multiindex moment ∧
    (∀ output, Summable (integratedMajorant outer inner multiindex moment output) ∧
      (∑' input, integratedMajorant outer inner multiindex moment output input) ≤
        spatialBound outer.rowBound inner.rowBound multiindex moment) ∧
    (∀ input, Summable (fun output => integratedMajorant outer inner multiindex moment output input) ∧
      (∑' output, integratedMajorant outer inner multiindex moment output input) ≤
        spatialBound outer.columnBound inner.columnBound multiindex moment)

def DominationGoal : Prop :=
  ∀ width : ℝ → ℝ, outer.envelope = radialEnvelope width → inner.envelope = radialEnvelope width →
    (∀ point ∈ domain, 0 ≤ width ‖point‖) → ∀ multiindex moment output input,
    ∀ᵐ pair ∂(parameterMeasure outerMeasure innerMeasure).prod (volume.restrict domain),
      ‖coefficientDerivative multiindex (coefficient outer inner output input) pair‖ *
        Grad.CellWeights.cellWeight (output - input) ^ moment * radialEnvelope width output input pair.2 ≤
          majorant outer inner multiindex moment output input pair.1

def ConstructionGoal : Prop :=
  ∀ width : ℝ → ℝ, outer.envelope = radialEnvelope width → inner.envelope = radialEnvelope width →
    (∀ point ∈ domain, 0 ≤ width ‖point‖) →
    ∃ data : RawKernelData (parameterMeasure outerMeasure innerMeasure) inputDimension outputDimension domain,
      DataSpecification outer inner (radialEnvelope width) data

variable [SigmaFinite outerMeasure] [SigmaFinite innerMeasure]

def ZeroRecordGoal : Prop :=
  ∀ envelope (data : RawKernelData (parameterMeasure outerMeasure innerMeasure) inputDimension outputDimension domain),
    DataSpecification outer inner envelope data →
      l2Data data (0, 0) 0 = Countable.composedData (l2Data outer (0, 0) 0) (l2Data inner (0, 0) 0)

def RealizationSpecification
    (data : RawKernelData (parameterMeasure outerMeasure innerMeasure) inputDimension outputDimension domain) : Prop :=
  Grad.FullCellKernel.kernel (l2Data data (0, 0) 0) =
    (Grad.FullCellKernel.kernel (l2Data outer (0, 0) 0)).comp
      (Grad.FullCellKernel.kernel (l2Data inner (0, 0) 0)) ∧
  (∀ multiindex moment,
    Grad.FullCellKernel.KernelSpec (l2Data data multiindex moment) (operator data multiindex moment) ∧
      ‖operator data multiindex moment‖ ≤ Real.sqrt
        (spatialBound outer.rowBound inner.rowBound multiindex moment *
          spatialBound outer.columnBound inner.columnBound multiindex moment)) ∧
  ∀ (field : FieldL2 inputDimension domain) (cells : Finset ℤ),
    (∀ input ∉ cells, fieldCellProjection inputDimension domain input field = 0) →
    ∀ᵐ point ∂volume.restrict domain, ∀ output : ℤ,
      operator data (0, 0) 0 field point output = ∑ input ∈ cells,
        ∫ parameter : Parameter Outer Inner,
          outer.coefficient output parameter.1 (parameter.2.1, point)
            (inner.coefficient parameter.1 input (parameter.2.2, outer.orthogonal parameter.2.1 point)
              (field (inner.orthogonal parameter.2.2 (outer.orthogonal parameter.2.1 point)) input))
          ∂parameterMeasure outerMeasure innerMeasure

def RealizationGoal : Prop :=
  ∀ envelope (data : RawKernelData (parameterMeasure outerMeasure innerMeasure) inputDimension outputDimension domain),
    DataSpecification outer inner envelope data → RealizationSpecification outer inner data

def GenericGoal : Prop :=
  ∃ data : RawKernelData (parameterMeasure outerMeasure innerMeasure) inputDimension outputDimension domain,
    DataSpecification outer inner unitEnvelope data ∧ RealizationSpecification outer inner data

def RadialGoal : Prop :=
  ∀ width : ℝ → ℝ, outer.envelope = radialEnvelope width → inner.envelope = radialEnvelope width →
    (∀ point ∈ domain, 0 ≤ width ‖point‖) →
    ∃ data : RawKernelData (parameterMeasure outerMeasure innerMeasure) inputDimension outputDimension domain,
      DataSpecification outer inner (radialEnvelope width) data ∧ RealizationSpecification outer inner data

def OriginalWidthGoal : Prop :=
  ∀ sigma gamma scale : ℝ,
    outer.envelope = Grad.AnalyticWeights.envelope sigma gamma scale →
    inner.envelope = Grad.AnalyticWeights.envelope sigma gamma scale →
    (∀ point ∈ domain, 0 ≤ Grad.AnalyticWeights.rate sigma gamma (scale * ‖point‖)) →
    ∃ data : RawKernelData (parameterMeasure outerMeasure innerMeasure) inputDimension outputDimension domain,
      DataSpecification outer inner (Grad.AnalyticWeights.envelope sigma gamma scale) data ∧
        RealizationSpecification outer inner data

def BlockGoal : Prop :=
  AllocationGoal ∧
  ∀ (Outer : Type outerUniverse) (Inner : Type innerUniverse) [MeasurableSpace Outer] [MeasurableSpace Inner]
    (outerMeasure : Measure Outer) (innerMeasure : Measure Inner) [SigmaFinite outerMeasure] [SigmaFinite innerMeasure]
    (inputDimension middleDimension outputDimension : ℕ) (domain : Set Spatial)
    (outer : RawKernelData outerMeasure middleDimension outputDimension domain)
    (inner : RawKernelData innerMeasure inputDimension middleDimension domain),
    UnitDataGoal outer ∧ UnitDataGoal inner ∧
      ChainFactorGoal outer ∧ DerivativeGoal outer inner ∧ DerivativeMeasurableGoal outer inner ∧
      MajorantGoal outer inner ∧ DominationGoal outer inner ∧ ConstructionGoal outer inner ∧
      ZeroRecordGoal outer inner ∧ RealizationGoal outer inner ∧ GenericGoal outer inner ∧
      RadialGoal outer inner ∧ OriginalWidthGoal outer inner

end Grad.RepresentedKernel.Composition.Spatial
