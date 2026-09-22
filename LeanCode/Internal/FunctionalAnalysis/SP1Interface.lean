import RK1Algebra
import OC2CoefficientComposition
import TensorCoefficientsInterface
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open scoped BigOperators ContDiff

universe valueUniverse outerUniverse innerUniverse

namespace Grad.RepresentedKernel.SpatialProduct

abbrev Word (rank : ℕ) := Fin rank → Fin 2

def subword {rank : ℕ} (word : Word rank) (selected : Finset (Fin rank)) : Word selected.card :=
  fun position => word (selected.orderEmbOfFin rfl position)

def selectedDerivative {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {rank : ℕ} (directions : Fin rank → Spatial) (selected : Finset (Fin rank))
    (function : Spatial → Value) (point : Spatial) : Value :=
  iteratedFDeriv ℝ selected.card function point
    (fun position => directions (selected.orderEmbOfFin rfl position))

def wordDerivative {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (rank : ℕ) (word : Word rank) (function : Spatial → Value) (point : Spatial) : Value :=
  iteratedFDeriv ℝ rank function point (fun position => spatialDirection (word position))

def twistedDerivative {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (rank : ℕ) (word : Word rank) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (function : Spatial → Value) (point : Spatial) : Value :=
  iteratedFDeriv ℝ rank function (orthogonal point)
    (fun position => orthogonal (spatialDirection (word position)))

def chainFactor (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (word target : Word rank) : ℝ :=
  Grad.TensorCoefficients.tensorCoefficient rank
    (Grad.OrthogonalCoefficients.coefficient orthogonal) word target

def allocationTerm {Outer : Type outerUniverse} {Inner : Type innerUniverse}
    {inputDimension middleDimension outputDimension : ℕ}
    (orthogonal : Outer → Spatial ≃ₗᵢ[ℝ] Spatial)
    (outer : ℤ → ℤ → Outer × Spatial → PhysicalValue middleDimension →L[ℂ] PhysicalValue outputDimension)
    (inner : ℤ → ℤ → Inner × Spatial → PhysicalValue inputDimension →L[ℂ] PhysicalValue middleDimension)
    (output input : ℤ) (parameter : ℤ × Outer × Inner) (rank : ℕ) (word : Word rank)
    (selected : Finset (Fin rank)) (point : Spatial) :
    PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension :=
  (wordDerivative selected.card (subword word selected)
    (fun source => outer output parameter.1 (parameter.2.1, source)) point).comp
  (twistedDerivative (selectedᶜ).card (subword word selectedᶜ) (orthogonal parameter.2.1)
    (fun source => inner parameter.1 input (parameter.2.2, source)) point)

def expandedTerm {Outer : Type outerUniverse} {Inner : Type innerUniverse}
    {inputDimension middleDimension outputDimension : ℕ}
    (orthogonal : Outer → Spatial ≃ₗᵢ[ℝ] Spatial)
    (outer : ℤ → ℤ → Outer × Spatial → PhysicalValue middleDimension →L[ℂ] PhysicalValue outputDimension)
    (inner : ℤ → ℤ → Inner × Spatial → PhysicalValue inputDimension →L[ℂ] PhysicalValue middleDimension)
    (output input : ℤ) (parameter : ℤ × Outer × Inner) (rank : ℕ) (word : Word rank)
    (selected : Finset (Fin rank)) (target : Word (selectedᶜ).card) (point : Spatial) :
    PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension :=
  chainFactor (selectedᶜ).card (orthogonal parameter.2.1) (subword word selectedᶜ) target •
    (wordDerivative selected.card (subword word selected)
      (fun source => outer output parameter.1 (parameter.2.1, source)) point).comp
    (wordDerivative (selectedᶜ).card target
      (fun source => inner parameter.1 input (parameter.2.2, source)) (orthogonal parameter.2.1 point))

def CoefficientSpecification {Outer : Type outerUniverse} {Inner : Type innerUniverse}
    {inputDimension middleDimension outputDimension : ℕ} (domain : Set Spatial)
    (orthogonal : Outer → Spatial ≃ₗᵢ[ℝ] Spatial)
    (outer : ℤ → ℤ → Outer × Spatial → PhysicalValue middleDimension →L[ℂ] PhysicalValue outputDimension)
    (inner : ℤ → ℤ → Inner × Spatial → PhysicalValue inputDimension →L[ℂ] PhysicalValue middleDimension) : Prop :=
  ∀ (output input : ℤ) (parameter : ℤ × Outer × Inner),
    ContDiffOn ℝ ∞ (composedCoefficient orthogonal outer inner output input parameter) domain ∧
      ∀ (rank : ℕ) (word : Word rank) (point : Spatial), point ∈ domain →
        wordDerivative rank word (composedCoefficient orthogonal outer inner output input parameter) point =
          ∑ selected : Finset (Fin rank),
            allocationTerm orthogonal outer inner output input parameter rank word selected point ∧
        wordDerivative rank word (composedCoefficient orthogonal outer inner output input parameter) point =
          ∑ selected : Finset (Fin rank), ∑ target : Word (selectedᶜ).card,
            expandedTerm orthogonal outer inner output input parameter rank word selected target point

def PositionGoal : Prop :=
  ∀ (rank : ℕ) (selected : Finset (Fin rank)),
    selected.card + (selectedᶜ).card = rank ∧
      StrictMono (selected.orderEmbOfFin rfl) ∧
      ∀ position : Fin selected.card, selected.orderEmbOfFin rfl position ∈ selected

def BilinearGoal : Prop :=
  ∀ (First Second Third : Type valueUniverse) [NormedAddCommGroup First] [NormedSpace ℝ First]
    [NormedAddCommGroup Second] [NormedSpace ℝ Second] [NormedAddCommGroup Third] [NormedSpace ℝ Third]
    (bilinear : First →L[ℝ] Second →L[ℝ] Third) (domain : Set Spatial), IsOpen domain →
    ∀ (first : Spatial → First) (second : Spatial → Second),
      ContDiffOn ℝ ∞ first domain → ContDiffOn ℝ ∞ second domain →
      ∀ (rank : ℕ) (directions : Fin rank → Spatial) (point : Spatial), point ∈ domain →
        iteratedFDeriv ℝ rank (fun source => bilinear (first source) (second source)) point directions =
          ∑ selected : Finset (Fin rank),
            bilinear (selectedDerivative directions selected first point)
              (selectedDerivative directions selectedᶜ second point)

def ChainGoal : Prop :=
  (∀ (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (word target : Word rank),
    chainFactor rank orthogonal word target =
      ∏ position, orthogonal (spatialDirection (word position)) (target position)) ∧
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (domain : Set Spatial), IsOpen domain → ∀ orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial,
      Grad.KernelPullback.Domain.Invariant domain orthogonal → ∀ function : Spatial → Value,
      ContDiffOn ℝ ∞ function domain → ∀ (rank : ℕ) (word : Word rank) (point : Spatial),
        point ∈ domain →
        wordDerivative rank word (fun source => function (orthogonal source)) point =
          twistedDerivative rank word orthogonal function point ∧
        twistedDerivative rank word orthogonal function point =
          ∑ target : Word rank, chainFactor rank orthogonal word target •
            wordDerivative rank target function (orthogonal point)

def CoefficientGoal : Prop :=
  ∀ (Outer : Type outerUniverse) (Inner : Type innerUniverse)
    (inputDimension middleDimension outputDimension : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ orthogonal : Outer → Spatial ≃ₗᵢ[ℝ] Spatial,
      (∀ parameter, Grad.KernelPullback.Domain.Invariant domain (orthogonal parameter)) →
    ∀ (outer : ℤ → ℤ → Outer × Spatial → PhysicalValue middleDimension →L[ℂ] PhysicalValue outputDimension)
      (inner : ℤ → ℤ → Inner × Spatial → PhysicalValue inputDimension →L[ℂ] PhysicalValue middleDimension),
      (∀ output middle parameter, ContDiffOn ℝ ∞ (fun point => outer output middle (parameter, point)) domain) →
      (∀ middle input parameter, ContDiffOn ℝ ∞ (fun point => inner middle input (parameter, point)) domain) →
      CoefficientSpecification domain orthogonal outer inner

def RawDataGoal : Prop :=
  ∀ (Outer : Type outerUniverse) (Inner : Type innerUniverse) [MeasurableSpace Outer] [MeasurableSpace Inner]
    (outerMeasure : Measure Outer) (innerMeasure : Measure Inner)
    (inputDimension middleDimension outputDimension : ℕ) (domain : Set Spatial)
    (outer : RawKernelData outerMeasure middleDimension outputDimension domain)
    (inner : RawKernelData innerMeasure inputDimension middleDimension domain),
      CoefficientSpecification domain outer.orthogonal outer.coefficient inner.coefficient

def CanonicalDerivativeGoal : Prop :=
  ∀ (Parameter : Type outerUniverse) (inputDimension outputDimension : ℕ)
    (coefficient : Parameter × Spatial → PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension)
    (multiindex : ℕ × ℕ) (pair : Parameter × Spatial),
    coefficientDerivative multiindex coefficient pair =
      wordDerivative (multiindex.1 + multiindex.2)
        (Grad.WeakTesting.Commutation.canonicalWord multiindex.1 multiindex.2)
        (fun point => coefficient (pair.1, point)) pair.2

def FirstOrderGoal : Prop :=
  ∀ (Outer : Type outerUniverse) (Inner : Type innerUniverse)
    (inputDimension middleDimension outputDimension : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ orthogonal : Outer → Spatial ≃ₗᵢ[ℝ] Spatial,
      (∀ parameter, Grad.KernelPullback.Domain.Invariant domain (orthogonal parameter)) →
    ∀ (outer : ℤ → ℤ → Outer × Spatial → PhysicalValue middleDimension →L[ℂ] PhysicalValue outputDimension)
      (inner : ℤ → ℤ → Inner × Spatial → PhysicalValue inputDimension →L[ℂ] PhysicalValue middleDimension),
      (∀ output middle parameter, ContDiffOn ℝ ∞ (fun point => outer output middle (parameter, point)) domain) →
      (∀ middle input parameter, ContDiffOn ℝ ∞ (fun point => inner middle input (parameter, point)) domain) →
      ∀ (output input : ℤ) (parameter : ℤ × Outer × Inner) (direction : Fin 2) (point : Spatial),
        point ∈ domain →
        fderiv ℝ (composedCoefficient orthogonal outer inner output input parameter) point (spatialDirection direction) =
          (fderiv ℝ (fun source => outer output parameter.1 (parameter.2.1, source)) point
            (spatialDirection direction)).comp
              (inner parameter.1 input (parameter.2.2, orthogonal parameter.2.1 point)) +
          (outer output parameter.1 (parameter.2.1, point)).comp
            (fderiv ℝ (fun source => inner parameter.1 input (parameter.2.2, source))
              (orthogonal parameter.2.1 point) (orthogonal parameter.2.1 (spatialDirection direction)))

def ZeroGoal : Prop :=
  (∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (function : Spatial → Value) (word : Word 0) (point : Spatial), wordDerivative 0 word function point = function point) ∧
  (∀ (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (word target : Word 0), chainFactor 0 orthogonal word target = 1) ∧
  ∀ (Outer : Type outerUniverse) (Inner : Type innerUniverse)
    (inputDimension middleDimension outputDimension : ℕ) (orthogonal : Outer → Spatial ≃ₗᵢ[ℝ] Spatial)
    (outer : ℤ → ℤ → Outer × Spatial → PhysicalValue middleDimension →L[ℂ] PhysicalValue outputDimension)
    (inner : ℤ → ℤ → Inner × Spatial → PhysicalValue inputDimension →L[ℂ] PhysicalValue middleDimension)
    (output input : ℤ) (parameter : ℤ × Outer × Inner) (word : Word 0) (point : Spatial),
    (∑ selected : Finset (Fin 0), allocationTerm orthogonal outer inner output input parameter 0 word selected point) =
      composedCoefficient orthogonal outer inner output input parameter point ∧
    (∑ selected : Finset (Fin 0), ∑ target : Word (selectedᶜ).card,
      expandedTerm orthogonal outer inner output input parameter 0 word selected target point) =
      composedCoefficient orthogonal outer inner output input parameter point

def BlockGoal : Prop :=
  PositionGoal ∧ BilinearGoal.{valueUniverse} ∧ ChainGoal.{valueUniverse} ∧
    CoefficientGoal.{outerUniverse, innerUniverse} ∧ RawDataGoal.{outerUniverse, innerUniverse} ∧
    CanonicalDerivativeGoal.{outerUniverse} ∧ FirstOrderGoal.{outerUniverse, innerUniverse} ∧
    ZeroGoal.{valueUniverse, outerUniverse, innerUniverse}

end Grad.RepresentedKernel.SpatialProduct
