import SP1Proof
import SP1Words

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open scoped BigOperators ContDiff

namespace Grad.RepresentedKernel.SpatialProduct

theorem exactBlock : BlockGoal := block
theorem exactPositions : PositionGoal := positions
theorem exactBilinear : BilinearGoal := bilinear
theorem exactChain : ChainGoal := chain
theorem exactCoefficients : CoefficientGoal := coefficients
theorem exactRawData : RawDataGoal := rawData
theorem exactCanonicalDerivative : CanonicalDerivativeGoal := canonicalDerivative
theorem exactFirstOrder : FirstOrderGoal := firstOrder
theorem exactZero : ZeroGoal := zero

theorem raw_allocation {Outer Inner : Type*} [MeasurableSpace Outer] [MeasurableSpace Inner]
    {outerMeasure : Measure Outer} {innerMeasure : Measure Inner}
    {inputDimension middleDimension outputDimension : ℕ} {domain : Set Spatial}
    (outer : RawKernelData outerMeasure middleDimension outputDimension domain)
    (inner : RawKernelData innerMeasure inputDimension middleDimension domain)
    (output middle input : ℤ) (outerParameter : Outer) (innerParameter : Inner)
    (rank : ℕ) (word : Word rank) (point : Spatial) (inside : point ∈ domain) :
    iteratedFDeriv ℝ rank
      (fun source => (outer.coefficient output middle (outerParameter, source)).comp
        (inner.coefficient middle input (innerParameter, outer.orthogonal outerParameter source)))
      point (fun position => spatialDirection (word position)) =
      ∑ selected : Finset (Fin rank),
        (iteratedFDeriv ℝ selected.card
          (fun source => outer.coefficient output middle (outerParameter, source)) point
          (fun position => spatialDirection (subword word selected position))).comp
        (iteratedFDeriv ℝ (selectedᶜ).card
          (fun source => inner.coefficient middle input (innerParameter, source))
          (outer.orthogonal outerParameter point)
          (fun position => outer.orthogonal outerParameter (spatialDirection (subword word selectedᶜ position)))) :=
  ((rawData Outer Inner outerMeasure innerMeasure inputDimension middleDimension outputDimension domain outer inner
    output input (middle, outerParameter, innerParameter)).2 rank word point inside).1

theorem raw_expanded {Outer Inner : Type*} [MeasurableSpace Outer] [MeasurableSpace Inner]
    {outerMeasure : Measure Outer} {innerMeasure : Measure Inner}
    {inputDimension middleDimension outputDimension : ℕ} {domain : Set Spatial}
    (outer : RawKernelData outerMeasure middleDimension outputDimension domain)
    (inner : RawKernelData innerMeasure inputDimension middleDimension domain)
    (output middle input : ℤ) (outerParameter : Outer) (innerParameter : Inner)
    (rank : ℕ) (word : Word rank) (point : Spatial) (inside : point ∈ domain) :
    wordDerivative rank word (composedCoefficient outer.orthogonal outer.coefficient inner.coefficient
      output input (middle, outerParameter, innerParameter)) point =
      ∑ selected : Finset (Fin rank), ∑ target : Word (selectedᶜ).card,
        (∏ position, outer.orthogonal outerParameter
          (spatialDirection (subword word selectedᶜ position)) (target position)) •
        (wordDerivative selected.card (subword word selected)
          (fun source => outer.coefficient output middle (outerParameter, source)) point).comp
        (wordDerivative (selectedᶜ).card target
          (fun source => inner.coefficient middle input (innerParameter, source))
          (outer.orthogonal outerParameter point)) :=
  ((rawData Outer Inner outerMeasure innerMeasure inputDimension middleDimension outputDimension domain outer inner
    output input (middle, outerParameter, innerParameter)).2 rank word point inside).2

theorem rank_zero {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (function : Spatial → Value) (point : Spatial) (word : Word 0) :
    wordDerivative 0 word function point = function point := zero.{_, 0, 0}.1 Value function word point

theorem zero_dimensions (domain : Set Spatial) (openDomain : IsOpen domain)
    (orthogonal : PUnit → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant domain (orthogonal parameter))
    (outer inner : ℤ → ℤ → PUnit × Spatial → PhysicalValue 0 →L[ℂ] PhysicalValue 0)
    (outerSmooth : ∀ output middle parameter, ContDiffOn ℝ ∞ (fun point => outer output middle (parameter, point)) domain)
    (innerSmooth : ∀ middle input parameter, ContDiffOn ℝ ∞ (fun point => inner middle input (parameter, point)) domain) :
    CoefficientSpecification domain orthogonal outer inner :=
  coefficients PUnit PUnit 0 0 0 domain openDomain orthogonal invariant outer inner outerSmooth innerSmooth

theorem count_total (rank : ℕ) (word : Word rank) :
    Grad.WeakTesting.Commutation.directionCount word 0 +
      Grad.WeakTesting.Commutation.directionCount word 1 = rank := by
  have cardinality := Fintype.card_congr (Equiv.sigmaFiberEquiv word)
  simpa only [Fintype.card_sigma, Fin.sum_univ_two, Fintype.card_fin,
    Grad.WeakTesting.Commutation.directionCount] using cardinality

theorem coefficient_word_canonical {Parameter : Type*} {inputDimension outputDimension : ℕ}
    {domain : Set Spatial} (openDomain : IsOpen domain)
    (coefficient : Parameter × Spatial → PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension)
    (parameter : Parameter)
    (smooth : ContDiffOn ℝ ∞ (fun point => coefficient (parameter, point)) domain)
    (rank : ℕ) (word : Word rank) (point : Spatial) (inside : point ∈ domain) :
    wordDerivative rank word (fun source => coefficient (parameter, source)) point =
      coefficientDerivative (Grad.WeakTesting.Commutation.directionCount word 0,
        Grad.WeakTesting.Commutation.directionCount word 1) coefficient (parameter, point) := by
  generalize zeroCount : Grad.WeakTesting.Commutation.directionCount word 0 = zeros
  generalize oneCount : Grad.WeakTesting.Commutation.directionCount word 1 = ones
  have cardinality : zeros + ones = rank := by rw [← zeroCount, ← oneCount]; exact count_total rank word
  subst rank
  exact wordDerivative_canonical openDomain zeros ones word zeroCount oneCount smooth inside

#check coefficients PUnit PUnit 0 2 3
#check coefficients PUnit PUnit 2 0 3
#check coefficients PUnit PUnit 2 3 0
#check fun (word : Word 0) (function : Spatial → PhysicalValue 0 →L[ℂ] PhysicalValue 0) => rank_zero function 0 word

end Grad.RepresentedKernel.SpatialProduct
