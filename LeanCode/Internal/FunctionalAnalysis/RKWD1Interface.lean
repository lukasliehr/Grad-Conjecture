import RK1Realization
import SP1Consumers
import SD1Consumer
import OJWeak

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open Grad.RepresentedKernel.SpatialProduct
open Grad.SpatialDilation (disk)
open scoped BigOperators ContDiff Topology

universe parameterUniverse

namespace Grad.RepresentedKernel.WeakDerivatives

def indexAdd (first second : ℕ × ℕ) : ℕ × ℕ :=
  (first.1 + second.1, first.2 + second.2)

def selectedIndex {rank : ℕ} (word : Word rank) (selected : Finset (Fin rank)) : ℕ × ℕ :=
  (Grad.WeakTesting.Commutation.directionCount (subword word selected) 0,
    Grad.WeakTesting.Commutation.directionCount (subword word selected) 1)

def chainProduct {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    {rank : ℕ} (word : Word rank) (selected : Finset (Fin rank))
    (target : Word (selectedᶜ).card) (parameter : Parameter) : ℝ :=
  chainFactor (selectedᶜ).card (data.orthogonal parameter) (subword word selectedᶜ) target

def allocatedCoefficient {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    {rank : ℕ} (word : Word rank) (selected : Finset (Fin rank))
    (target : Word (selectedᶜ).card) (output input : ℤ) (pair : Parameter × Spatial) :
    PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension :=
  (chainProduct data word selected target pair.1 : ℂ) •
    coefficientDerivative (selectedIndex word selected) (data.coefficient output input) pair

def allocatedMajorant {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    {rank : ℕ} (word : Word rank) (selected : Finset (Fin rank))
    (multiindex : ℕ × ℕ) (moment : ℕ) (output input : ℤ) (parameter : Parameter) : ℝ :=
  data.majorant (indexAdd multiindex (selectedIndex word selected)) moment output input parameter

def allocatedRowBound {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    {rank : ℕ} (word : Word rank) (selected : Finset (Fin rank))
    (multiindex : ℕ × ℕ) (moment : ℕ) : ℝ :=
  data.rowBound (indexAdd multiindex (selectedIndex word selected)) moment

def allocatedColumnBound {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    {rank : ℕ} (word : Word rank) (selected : Finset (Fin rank))
    (multiindex : ℕ × ℕ) (moment : ℕ) : ℝ :=
  data.columnBound (indexAdd multiindex (selectedIndex word selected)) moment

def AllocationSpecification {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    {rank : ℕ} (word : Word rank) (selected : Finset (Fin rank))
    (target : Word (selectedᶜ).card)
    (allocated : RawKernelData measure inputDimension outputDimension domain) : Prop :=
  allocated.orthogonal = data.orthogonal ∧
    allocated.coefficient = allocatedCoefficient data word selected target ∧
    allocated.envelope = data.envelope ∧
    allocated.majorant = allocatedMajorant data word selected ∧
    allocated.rowBound = allocatedRowBound data word selected ∧
    allocated.columnBound = allocatedColumnBound data word selected

abbrev AllocatedFamily {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    (measure : Measure Parameter) (inputDimension outputDimension : ℕ) (domain : Set Spatial)
    (rank : ℕ) :=
  (selected : Finset (Fin rank)) → Word (selectedᶜ).card →
    RawKernelData measure inputDimension outputDimension domain

def FamilySpecification {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    {rank : ℕ} (word : Word rank)
    (family : AllocatedFamily measure inputDimension outputDimension domain rank) : Prop :=
  ∀ selected target, AllocationSpecification data word selected target (family selected target)

def inputDerivative (dimension order rank weight : ℕ) (domain : Set Spatial)
    (bound : rank ≤ order) (jet : Grad.WeightedJets.GraphGrade dimension order weight domain)
    (selected : Finset (Fin rank)) (target : Word (selectedᶜ).card) :
    FieldL2 dimension domain :=
  Grad.WeightedJets.Ordered.orderedDerivative dimension order (selectedᶜ).card domain
    (fun _ => weight) (by
      have complementBound : (selectedᶜ).card ≤ rank := by
        simpa only [Fintype.card_fin] using Finset.card_le_univ selectedᶜ
      exact complementBound.trans bound) jet target

def derivativeCandidate {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension order rank weight : ℕ} {radius : ℝ}
    (_data : RawKernelData measure inputDimension outputDimension (disk radius))
    (_word : Word rank) (bound : rank ≤ order)
    (jet : Grad.WeightedJets.GraphGrade inputDimension order weight (disk radius))
    (family : AllocatedFamily measure inputDimension outputDimension (disk radius) rank) :
    FieldL2 outputDimension (disk radius) :=
  ∑ selected : Finset (Fin rank), ∑ target : Word (selectedᶜ).card,
    operator (family selected target) (0, 0) 0
      (inputDerivative inputDimension order rank weight (disk radius) bound jet selected target)

def ChainProductGoal : Prop :=
  ∀ (Parameter : Type parameterUniverse) [MeasurableSpace Parameter]
    (measure : Measure Parameter) (inputDimension outputDimension rank : ℕ)
    (domain : Set Spatial)
    (data : RawKernelData measure inputDimension outputDimension domain)
    (word : Word rank) (selected : Finset (Fin rank)) (target : Word (selectedᶜ).card),
    Measurable (chainProduct data word selected target) ∧
      ∀ parameter, |chainProduct data word selected target parameter| ≤ 1

def AllocationIndexGoal : Prop :=
  ∀ (rank : ℕ) (word : Word rank) (selected : Finset (Fin rank)),
    (selectedIndex word selected).1 + (selectedIndex word selected).2 = selected.card

def AllocationDataGoal : Prop :=
  ∀ (Parameter : Type parameterUniverse) [MeasurableSpace Parameter]
    (measure : Measure Parameter) (inputDimension outputDimension rank : ℕ)
    (domain : Set Spatial)
    (data : RawKernelData measure inputDimension outputDimension domain)
    (word : Word rank) (selected : Finset (Fin rank)) (target : Word (selectedᶜ).card),
    ∃ allocated : RawKernelData measure inputDimension outputDimension domain,
      AllocationSpecification data word selected target allocated

def AllocationCLMGoal : Prop :=
  ∀ (Parameter : Type parameterUniverse) [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    (inputDimension outputDimension rank : ℕ) (domain : Set Spatial)
    (data : RawKernelData measure inputDimension outputDimension domain)
    (word : Word rank)
    (family : AllocatedFamily measure inputDimension outputDimension domain rank),
    FamilySpecification data word family →
    ∀ (selected : Finset (Fin rank)) (target : Word (selectedᶜ).card)
      (multiindex : ℕ × ℕ) (moment : ℕ),
      ‖operator (family selected target) multiindex moment‖ ≤
        Real.sqrt (allocatedRowBound data word selected multiindex moment *
          allocatedColumnBound data word selected multiindex moment)

def CoreIBPGoal : Prop :=
  ∀ (Parameter : Type parameterUniverse) [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    (inputDimension outputDimension order rank weight : ℕ)
    (radius : ℝ) (_positiveRadius : 0 < radius)
    (data : RawKernelData measure inputDimension outputDimension (disk radius))
    (word : Word rank) (bound : rank ≤ order)
    (family : AllocatedFamily measure inputDimension outputDimension (disk radius) rank),
    FamilySpecification data word family →
    ∀ (jet : Grad.WeightedJets.GraphGrade inputDimension order weight (disk radius))
      (function : Spatial → CellValues inputDimension) (cells : Finset ℤ),
      Grad.SmoothDensity.CoreLaws inputDimension function cells →
      Grad.SmoothDensity.Realizes inputDimension (disk radius) (.graph order weight) function jet →
      ∀ (cell : ℤ) (vector : PhysicalValue outputDimension) (test : Spatial → ℝ),
        ContDiff ℝ ∞ test → HasCompactSupport test → tsupport test ⊆ disk radius →
        (∫ point in disk radius, test point • inner ℂ vector
          (derivativeCandidate data word bound jet family point cell)) =
          (-1 : ℂ) ^ rank * ∫ point in disk radius,
            Grad.WeakTesting.orderedTestDerivative rank word test point • inner ℂ vector
              (operator data (0, 0) 0
                (Grad.WeightedJets.base inputDimension order (disk radius) (fun _ => weight) jet)
                point cell)

def ClosedWeakGoal : Prop :=
  ∀ (dimension rank : ℕ) (domain : Set Spatial) (word : Word rank)
    (fields derivatives : ℕ → FieldL2 dimension domain)
    (field derivative : FieldL2 dimension domain),
    Filter.Tendsto fields Filter.atTop (𝓝 field) →
    Filter.Tendsto derivatives Filter.atTop (𝓝 derivative) →
    (∀ number, Grad.WeakTesting.Commutation.HasWeakOrderedDerivative
      dimension domain rank word (fields number) (derivatives number)) →
    Grad.WeakTesting.Commutation.HasWeakOrderedDerivative dimension domain rank word field derivative

def DensityPassageGoal : Prop :=
  ∀ (Parameter : Type parameterUniverse) [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    (inputDimension outputDimension order rank weight : ℕ)
    (radius : ℝ) (_positiveRadius : 0 < radius)
    (data : RawKernelData measure inputDimension outputDimension (disk radius))
    (word : Word rank) (bound : rank ≤ order)
    (family : AllocatedFamily measure inputDimension outputDimension (disk radius) rank),
    FamilySpecification data word family →
    ∀ jet : Grad.WeightedJets.GraphGrade inputDimension order weight (disk radius),
      Grad.WeakTesting.Commutation.HasWeakOrderedDerivative outputDimension (disk radius) rank word
        (operator data (0, 0) 0
          (Grad.WeightedJets.base inputDimension order (disk radius) (fun _ => weight) jet))
        (derivativeCandidate data word bound jet family)

def RankZeroGoal : Prop :=
  ∀ (Parameter : Type parameterUniverse) [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    (inputDimension outputDimension order weight : ℕ) (radius : ℝ)
    (data : RawKernelData measure inputDimension outputDimension (disk radius))
    (word : Word 0)
    (family : AllocatedFamily measure inputDimension outputDimension (disk radius) 0),
    FamilySpecification data word family →
    ∀ jet : Grad.WeightedJets.GraphGrade inputDimension order weight (disk radius),
      derivativeCandidate data word (Nat.zero_le order) jet family =
        operator data (0, 0) 0
          (Grad.WeightedJets.base inputDimension order (disk radius) (fun _ => weight) jet)

def BlockGoal : Prop :=
  ChainProductGoal.{parameterUniverse} ∧ AllocationIndexGoal ∧
    AllocationDataGoal.{parameterUniverse} ∧ AllocationCLMGoal.{parameterUniverse} ∧
    CoreIBPGoal.{parameterUniverse} ∧ ClosedWeakGoal ∧
    DensityPassageGoal.{parameterUniverse} ∧ RankZeroGoal.{parameterUniverse}

end Grad.RepresentedKernel.WeakDerivatives
