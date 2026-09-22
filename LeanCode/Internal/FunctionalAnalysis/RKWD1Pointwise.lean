import RKWD1Allocation
import RKWD1CoreRepresentatives

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open Grad.RepresentedKernel.SpatialProduct
open scoped BigOperators ContDiff Topology

universe parameterUniverse

namespace Grad.RepresentedKernel.WeakDerivatives

theorem kernelProduct_smooth {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} {inputDimension outputDimension : ℕ}
    {domain : Set Spatial} (data : RawKernelData measure inputDimension outputDimension domain)
    (function : Spatial → CellValues inputDimension) (smooth : ContDiff ℝ ∞ function)
    (output input : ℤ) (parameter : Parameter) :
    ContDiffOn ℝ ∞ (fun source => data.coefficient output input (parameter, source)
      (function (data.orthogonal parameter source) input)) domain := by
  let coefficient := fun source => data.coefficient output input (parameter, source)
  let coordinate := fun source => function source input
  let transported := fun source => coordinate (data.orthogonal parameter source)
  let complexApply :
      (PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension) →L[ℂ]
        PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension :=
    (ContinuousLinearMap.apply ℂ (PhysicalValue outputDimension)).flip
  let realApply :
      (PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension) →L[ℝ]
        PhysicalValue inputDimension →L[ℝ] PhysicalValue outputDimension :=
    complexApply.bilinearRestrictScalars ℝ
  have coordinateSmooth : ContDiff ℝ ∞ coordinate :=
    ((lp.evalCLM ℂ (fun _ : ℤ => PhysicalValue inputDimension) 2 input).restrictScalars ℝ).contDiff.comp smooth
  have transportedSmooth : ContDiffOn ℝ ∞ transported domain :=
    coordinateSmooth.contDiffOn.comp
      (data.orthogonal parameter).toContinuousLinearEquiv.contDiff.contDiffOn
      (fun source sourceInside => (data.invariant parameter source).mpr sourceInside)
  exact realApply.isBoundedBilinearMap.contDiff.comp₂_contDiffOn
    (data.coefficientSmooth output input parameter) transportedSmooth

theorem kernelProductInner_smooth {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} {inputDimension outputDimension : ℕ}
    {domain : Set Spatial} (data : RawKernelData measure inputDimension outputDimension domain)
    (function : Spatial → CellValues inputDimension) (smooth : ContDiff ℝ ∞ function)
    (output input : ℤ) (parameter : Parameter) (vector : PhysicalValue outputDimension) :
    ContDiffOn ℝ ∞ (fun source => inner ℂ vector
      (data.coefficient output input (parameter, source)
        (function (data.orthogonal parameter source) input))) domain := by
  exact ((innerSL ℂ vector).restrictScalars ℝ).contDiff.fun_comp_contDiffOn
    (kernelProduct_smooth data function smooth output input parameter)

theorem productDerivative_expansion {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} {inputDimension outputDimension rank : ℕ}
    {domain : Set Spatial} (data : RawKernelData measure inputDimension outputDimension domain)
    (function : Spatial → CellValues inputDimension)
    (smooth : ContDiff ℝ ∞ function) (word : Word rank)
    (output input : ℤ) (parameter : Parameter) (point : Spatial) (inside : point ∈ domain) :
    Grad.Mollifier.Pointwise.orderedDerivative rank word
        (fun source => data.coefficient output input (parameter, source)
          (function (data.orthogonal parameter source) input)) point =
      ∑ selected : Finset (Fin rank), ∑ target : Word (selectedᶜ).card,
        allocatedCoefficient data word selected target output input (parameter, point)
          (Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function
            (data.orthogonal parameter point) input) := by
  let coefficient := fun source => data.coefficient output input (parameter, source)
  let coordinate := fun source => function source input
  let transported := fun source => coordinate (data.orthogonal parameter source)
  let complexApply :
      (PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension) →L[ℂ]
        PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension :=
    (ContinuousLinearMap.apply ℂ (PhysicalValue outputDimension)).flip
  let realApply :
      (PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension) →L[ℝ]
        PhysicalValue inputDimension →L[ℝ] PhysicalValue outputDimension :=
    complexApply.bilinearRestrictScalars ℝ
  have coefficientSmooth : ContDiffOn ℝ ∞ coefficient domain :=
    data.coefficientSmooth output input parameter
  have coordinateSmooth : ContDiff ℝ ∞ coordinate :=
    ((lp.evalCLM ℂ (fun _ : ℤ => PhysicalValue inputDimension) 2 input).restrictScalars ℝ).contDiff.comp smooth
  have transportedSmooth : ContDiffOn ℝ ∞ transported domain :=
    coordinateSmooth.contDiffOn.comp
      (data.orthogonal parameter).toContinuousLinearEquiv.contDiff.contDiffOn
      (fun source sourceInside => (data.invariant parameter source).mpr sourceInside)
  have expansion := Grad.RepresentedKernel.SpatialProduct.exactBilinear
    _ _ _ realApply domain data.domainOpen coefficient transported coefficientSmooth transportedSmooth rank
      (fun position => spatialDirection (word position)) point inside
  change Grad.RepresentedKernel.SpatialProduct.wordDerivative rank word
      (fun source => realApply (coefficient source) (transported source)) point = _
  refine expansion.trans ?_
  apply Finset.sum_congr rfl
  intro selected _membership
  have coefficientIdentity := Grad.RepresentedKernel.SpatialProduct.coefficient_word_canonical
    data.domainOpen (data.coefficient output input) parameter coefficientSmooth selected.card
      (subword word selected) point inside
  have chainIdentity := Grad.RepresentedKernel.SpatialProduct.exactChain.2
    (PhysicalValue inputDimension) domain data.domainOpen (data.orthogonal parameter)
      (data.invariant parameter) coordinate coordinateSmooth.contDiffOn (selectedᶜ).card
      (subword word selectedᶜ) point inside
  change realApply
      (wordDerivative selected.card (subword word selected) coefficient point)
      (wordDerivative (selectedᶜ).card (subword word selectedᶜ) transported point) = _
  rw [coefficientIdentity, chainIdentity.1, chainIdentity.2, map_sum]
  apply Finset.sum_congr rfl
  intro target _membership
  have coordinateIdentity := Grad.SmoothDensity.orderedDerivative_map
    (lp.evalCLM ℂ (fun _ : ℤ => PhysicalValue inputDimension) 2 input)
      (selectedᶜ).card target function smooth (data.orthogonal parameter point)
  change wordDerivative (selectedᶜ).card target coordinate (data.orthogonal parameter point) =
      Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function
        (data.orthogonal parameter point) input at coordinateIdentity
  rw [coordinateIdentity]
  change coefficientDerivative (selectedIndex word selected) (data.coefficient output input)
      (parameter, point)
        (chainProduct data word selected target parameter •
          Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function
            (data.orthogonal parameter point) input) =
    ((chainProduct data word selected target parameter : ℂ) •
      coefficientDerivative (selectedIndex word selected) (data.coefficient output input)
        (parameter, point))
      (Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function
        (data.orthogonal parameter point) input)
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rw [map_smul]
  rfl

theorem productInnerDerivative_expansion {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} {inputDimension outputDimension rank : ℕ}
    {domain : Set Spatial} (data : RawKernelData measure inputDimension outputDimension domain)
    (function : Spatial → CellValues inputDimension)
    (smooth : ContDiff ℝ ∞ function) (word : Word rank)
    (output input : ℤ) (parameter : Parameter) (point : Spatial) (inside : point ∈ domain)
    (vector : PhysicalValue outputDimension) :
    wordDerivative rank word (fun source => inner ℂ vector
        (data.coefficient output input (parameter, source)
          (function (data.orthogonal parameter source) input))) point =
      inner ℂ vector (∑ selected : Finset (Fin rank), ∑ target : Word (selectedᶜ).card,
        allocatedCoefficient data word selected target output input (parameter, point)
          (Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function
            (data.orthogonal parameter point) input)) := by
  let product := fun source => data.coefficient output input (parameter, source)
    (function (data.orthogonal parameter source) input)
  let functional := (innerSL ℂ vector).restrictScalars ℝ
  have productSmooth : ContDiffAt ℝ ∞ product point :=
    (kernelProduct_smooth data function smooth output input parameter).contDiffAt
      (data.domainOpen.mem_nhds inside)
  have mapping := functional.iteratedFDeriv_comp_left productSmooth
    (by exact_mod_cast (le_top : (rank : ℕ∞) ≤ ⊤))
  change iteratedFDeriv ℝ rank (functional ∘ product) point
      (fun position => spatialDirection (word position)) = _
  rw [mapping]
  change functional (wordDerivative rank word product point) = _
  exact congrArg functional
    (productDerivative_expansion data function smooth word output input parameter point inside)

end Grad.RepresentedKernel.WeakDerivatives
