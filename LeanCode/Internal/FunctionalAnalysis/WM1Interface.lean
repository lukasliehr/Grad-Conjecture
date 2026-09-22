import WeightedJetProof
import WTCInterface
import MP1Interface

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeakTesting.Commutation (HasWeakOrderedDerivative)
open scoped Topology ContDiff BigOperators

namespace Grad.Mollifier.WeakJets

def shiftedTest (offset : Spatial) (test : Spatial → ℝ) : Spatial → ℝ :=
  fun point => test (point + offset)

def reflectedKernel (point : Spatial) (kernel : Spatial → ℝ) : Spatial → ℝ :=
  fun source => kernel (point - source)

def averageTuple (dimension order : ℕ) (kernel : Spatial → ℝ)
    (tuple : JetTuple dimension order Set.univ) : JetTuple dimension order Set.univ :=
  graphOfCoordinates (fun index => Grad.SpatialTranslation.average (CellValues dimension) kernel (tuple index))

def regularizedTuple (dimension order : ℕ) (epsilon : ℝ)
    (tuple : JetTuple dimension order Set.univ) : JetTuple dimension order Set.univ :=
  averageTuple dimension order (Pointwise.scaledEta epsilon) tuple

def LiftSpecification (dimension order : ℕ) (exponent : JetIndex order → ℕ)
    (kernel : Spatial → ℝ)
    (operator : WJet dimension order Set.univ exponent →L[ℂ] WJet dimension order Set.univ exponent) :
    Prop :=
  (∀ jet : WJet dimension order Set.univ exponent,
    (operator jet).val = averageTuple dimension order kernel jet.val) ∧
  (∀ jet : WJet dimension order Set.univ exponent,
    base dimension order Set.univ exponent (operator jet) =
      Grad.SpatialTranslation.average (CellValues dimension) kernel
        (base dimension order Set.univ exponent jet))

def TestGoal : Prop :=
  ∀ (test : Spatial → ℝ), ContDiff ℝ ∞ test → HasCompactSupport test →
    ∀ offset : Spatial,
    ContDiff ℝ ∞ (shiftedTest offset test) ∧ HasCompactSupport (shiftedTest offset test) ∧
    ContDiff ℝ ∞ (reflectedKernel offset test) ∧ HasCompactSupport (reflectedKernel offset test) ∧
    (∀ (rank : ℕ) (word : Fin rank → Fin 2) (point : Spatial),
      Grad.WeakTesting.orderedTestDerivative rank word (shiftedTest offset test) point =
        Grad.WeakTesting.orderedTestDerivative rank word test (point + offset)) ∧
    (∀ (rank : ℕ) (word : Fin rank → Fin 2) (point : Spatial),
      Grad.WeakTesting.orderedTestDerivative rank word (reflectedKernel offset test) point =
        (-1 : ℝ) ^ rank * Grad.WeakTesting.orderedTestDerivative rank word test (offset - point))

def KernelWeakGoal : Prop :=
  ∀ (dimension rank : ℕ) (word : Fin rank → Fin 2) (field derivative : FieldL2 dimension Set.univ),
    HasWeakOrderedDerivative dimension Set.univ rank word field derivative →
    ∀ kernel : Spatial → ℝ, ContDiff ℝ ∞ kernel → HasCompactSupport kernel →
      Pointwise.orderedDerivative rank word
        (Pointwise.smoothRepresentative (CellValues dimension) kernel field) =
      Pointwise.smoothRepresentative (CellValues dimension) kernel derivative

def TranslationWeakGoal : Prop :=
  ∀ (dimension rank : ℕ) (word : Fin rank → Fin 2) (field derivative : FieldL2 dimension Set.univ),
    HasWeakOrderedDerivative dimension Set.univ rank word field derivative →
    ∀ offset : Spatial,
      HasWeakOrderedDerivative dimension Set.univ rank word
        (Grad.SpatialTranslation.translation (CellValues dimension) offset field)
        (Grad.SpatialTranslation.translation (CellValues dimension) offset derivative)

def AveragedWeakGoal : Prop :=
  ∀ (dimension rank : ℕ) (word : Fin rank → Fin 2) (field derivative : FieldL2 dimension Set.univ),
    HasWeakOrderedDerivative dimension Set.univ rank word field derivative →
    ∀ kernel : Spatial → ℝ, Integrable kernel volume →
      HasWeakOrderedDerivative dimension Set.univ rank word
        (Grad.SpatialTranslation.average (CellValues dimension) kernel field)
        (Grad.SpatialTranslation.average (CellValues dimension) kernel derivative)

def CellNaturalityGoal : Prop :=
  ∀ (dimension : ℕ) (kernel : Spatial → ℝ), Integrable kernel volume →
    (∀ (field : FieldL2 dimension Set.univ) (cell : ℤ),
      fieldCellProjection dimension Set.univ cell
          (Grad.SpatialTranslation.average (CellValues dimension) kernel field) =
        Grad.SpatialTranslation.average (PhysicalValue dimension) kernel
          (fieldCellProjection dimension Set.univ cell field)) ∧
    (∀ (weight : ℕ) (field : FieldL2 dimension Set.univ),
      Grad.CellWeights.inverseFieldCLM dimension Set.univ weight
          (Grad.SpatialTranslation.average (CellValues dimension) kernel field) =
        Grad.SpatialTranslation.average (CellValues dimension) kernel
          (Grad.CellWeights.inverseFieldCLM dimension Set.univ weight field))

def AmbientGoal : Prop :=
  ∀ (dimension order : ℕ) (kernel : Spatial → ℝ), Integrable kernel volume →
    ∀ tuple : JetTuple dimension order Set.univ,
    (∀ index : JetIndex order, averageTuple dimension order kernel tuple index =
      Grad.SpatialTranslation.average (CellValues dimension) kernel (tuple index)) ∧
    (∀ exponent : JetIndex order → ℕ,
      ambientBase dimension order Set.univ exponent (averageTuple dimension order kernel tuple) =
        Grad.SpatialTranslation.average (CellValues dimension) kernel
          (ambientBase dimension order Set.univ exponent tuple)) ∧
    ‖averageTuple dimension order kernel tuple‖ ^ 2 =
      (∑ index, ‖Grad.SpatialTranslation.average (CellValues dimension) kernel (tuple index)‖ ^ 2) ∧
    ‖averageTuple dimension order kernel tuple‖ ≤ Grad.SpatialTranslation.kernelL1 kernel * ‖tuple‖

def GraphGoal : Prop :=
  ∀ (dimension order : ℕ) (exponent : JetIndex order → ℕ) (kernel : Spatial → ℝ),
    Integrable kernel volume → ∀ jet : WJet dimension order Set.univ exponent,
      averageTuple dimension order kernel jet.val ∈ jetGraph dimension order Set.univ exponent

def IntegralGoal : Prop :=
  ∀ (dimension order : ℕ) (exponent : JetIndex order → ℕ) (kernel : Spatial → ℝ),
    Integrable kernel volume → ∀ (jet : WJet dimension order Set.univ exponent)
    (index : JetIndex order) (cell : ℤ) (vector : PhysicalValue dimension)
    (test : TestFunction Set.univ),
    (∫ point : Spatial, test.toFun point •
      inner ℂ vector (averageTuple dimension order kernel jet.val index point cell)) =
      ((-1 : ℂ) ^ degree index * Grad.CellWeights.positiveFactor (exponent index) cell) *
        ∫ point : Spatial, Grad.WeakTesting.orderedTestDerivative (degree index) (derivativeWord index)
          test.toFun point • inner ℂ vector
            (Grad.SpatialTranslation.average (CellValues dimension) kernel
              (base dimension order Set.univ exponent jet) point cell)

def LiftGoal : Prop :=
  ∀ (dimension order : ℕ) (exponent : JetIndex order → ℕ) (kernel : Spatial → ℝ),
    Integrable kernel volume →
    ∃ operator : WJet dimension order Set.univ exponent →L[ℂ] WJet dimension order Set.univ exponent,
      LiftSpecification dimension order exponent kernel operator ∧
      ‖operator‖ ≤ Grad.SpatialTranslation.kernelL1 kernel

def ContractionGoal : Prop :=
  ∀ (dimension order : ℕ) (exponent : JetIndex order → ℕ) (kernel : Spatial → ℝ),
    Integrable kernel volume → (∀ᵐ point ∂volume, 0 ≤ kernel point) → (∫ point, kernel point) = 1 →
    (∀ jet : WJet dimension order Set.univ exponent,
      ‖averageTuple dimension order kernel jet.val‖ ≤ ‖jet‖) ∧
    (∀ operator : WJet dimension order Set.univ exponent →L[ℂ] WJet dimension order Set.univ exponent,
      LiftSpecification dimension order exponent kernel operator → ‖operator‖ ≤ 1)

def ApproximationGoal : Prop :=
  ∀ (dimension order : ℕ) (exponent : JetIndex order → ℕ)
    (jet : WJet dimension order Set.univ exponent),
    Filter.Tendsto (fun epsilon : ℝ => regularizedTuple dimension order epsilon jet.val)
      (𝓝[>] 0) (𝓝 jet.val)

def RegularizationGoal : Prop :=
  ∀ (dimension order : ℕ) (exponent : JetIndex order → ℕ),
    ∃ regularizer : ℝ → WJet dimension order Set.univ exponent →L[ℂ]
      WJet dimension order Set.univ exponent,
    (∀ epsilon : ℝ, 0 < epsilon →
      LiftSpecification dimension order exponent (Pointwise.scaledEta epsilon) (regularizer epsilon) ∧
      ‖regularizer epsilon‖ ≤ 1) ∧
    (∀ jet : WJet dimension order Set.univ exponent,
      Filter.Tendsto (fun epsilon : ℝ => regularizer epsilon jet) (𝓝[>] 0) (𝓝 jet))

def SmoothGoal : Prop :=
  ∀ (dimension order : ℕ) (exponent : JetIndex order → ℕ) (epsilon : ℝ), 0 < epsilon →
    ∀ jet : WJet dimension order Set.univ exponent,
    ContDiff ℝ ∞ (Pointwise.smoothRepresentative (CellValues dimension) (Pointwise.scaledEta epsilon)
      (base dimension order Set.univ exponent jet)) ∧
    (∀ index : JetIndex order,
      ContDiff ℝ ∞ (Pointwise.smoothRepresentative (CellValues dimension) (Pointwise.scaledEta epsilon)
        (jet.val index)) ∧
      regularizedTuple dimension order epsilon jet.val index =ᵐ[volume]
        Pointwise.smoothRepresentative (CellValues dimension) (Pointwise.scaledEta epsilon) (jet.val index) ∧
      Grad.CellWeights.inverseFieldCLM dimension Set.univ (exponent index)
          (regularizedTuple dimension order epsilon jet.val index) =ᵐ[volume]
        Pointwise.orderedDerivative (degree index) (derivativeWord index)
          (Pointwise.smoothRepresentative (CellValues dimension) (Pointwise.scaledEta epsilon)
            (base dimension order Set.univ exponent jet)) ∧
      MemLp (Pointwise.orderedDerivative (degree index) (derivativeWord index)
        (Pointwise.smoothRepresentative (CellValues dimension) (Pointwise.scaledEta epsilon)
          (base dimension order Set.univ exponent jet))) 2 volume ∧
      (∀ (point : Spatial) (cell : ℤ),
        Pointwise.smoothRepresentative (CellValues dimension) (Pointwise.scaledEta epsilon)
            (jet.val index) point cell =
          Grad.CellWeights.positiveFactor (exponent index) cell •
            Pointwise.orderedDerivative (degree index) (derivativeWord index)
              (Pointwise.smoothRepresentative (CellValues dimension) (Pointwise.scaledEta epsilon)
                (base dimension order Set.univ exponent jet)) point cell))

def ZeroGoal : Prop :=
  (∀ (dimension : ℕ) (exponent : JetIndex 0 → ℕ) (epsilon : ℝ), 0 < epsilon →
    ∀ jet : WJet dimension 0 Set.univ exponent,
      averageTuple dimension 0 (Pointwise.scaledEta epsilon) jet.val ∈
        jetGraph dimension 0 Set.univ exponent) ∧
  (∀ (order : ℕ) (exponent : JetIndex order → ℕ) (epsilon : ℝ), 0 < epsilon →
    ∀ jet : WJet 0 order Set.univ exponent, regularizedTuple 0 order epsilon jet.val = 0)

def IndependentGoal : Prop := TestGoal ∧ KernelWeakGoal ∧ TranslationWeakGoal

def DependentGoal : Prop :=
  AveragedWeakGoal ∧ CellNaturalityGoal ∧ AmbientGoal ∧ GraphGoal ∧ IntegralGoal ∧
    LiftGoal ∧ ContractionGoal ∧ ApproximationGoal ∧ RegularizationGoal ∧ SmoothGoal ∧ ZeroGoal

def BlockGoal : Prop := IndependentGoal ∧ DependentGoal

end Grad.Mollifier.WeakJets
