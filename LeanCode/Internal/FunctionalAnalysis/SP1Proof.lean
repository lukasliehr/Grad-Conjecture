import SP1Bilinear
import SP1Chain

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open scoped BigOperators ContDiff Topology

namespace Grad.RepresentedKernel.SpatialProduct

theorem allocation_expansion {Outer Inner : Type*}
    {inputDimension middleDimension outputDimension : ℕ}
    (orthogonal : Outer → Spatial ≃ₗᵢ[ℝ] Spatial)
    (outer : ℤ → ℤ → Outer × Spatial → PhysicalValue middleDimension →L[ℂ] PhysicalValue outputDimension)
    (inner : ℤ → ℤ → Inner × Spatial → PhysicalValue inputDimension →L[ℂ] PhysicalValue middleDimension)
    (output input : ℤ) (parameter : ℤ × Outer × Inner) (rank : ℕ) (word : Word rank)
    (selected : Finset (Fin rank)) (point : Spatial) :
    allocationTerm orthogonal outer inner output input parameter rank word selected point =
      ∑ target : Word (selectedᶜ).card,
        expandedTerm orthogonal outer inner output input parameter rank word selected target point := by
  unfold allocationTerm
  rw [twisted_expansion]
  apply ContinuousLinearMap.ext
  intro value
  simp only [expandedTerm, sum_apply, ContinuousLinearMap.comp_apply, smul_apply, map_sum]
  apply Finset.sum_congr rfl
  intro target _
  exact ((wordDerivative selected.card (subword word selected)
    (fun source => outer output parameter.1 (parameter.2.1, source)) point).restrictScalars ℝ).map_smul _ _

theorem coefficients : CoefficientGoal := by
  intro Outer Inner inputDimension middleDimension outputDimension domain openDomain orthogonal invariant
    outer inner outerSmooth innerSmooth output input parameter
  let first := fun source => outer output parameter.1 (parameter.2.1, source)
  let second := fun source => inner parameter.1 input (parameter.2.2, orthogonal parameter.2.1 source)
  let composition := (ContinuousLinearMap.compL ℂ (PhysicalValue inputDimension)
    (PhysicalValue middleDimension) (PhysicalValue outputDimension)).bilinearRestrictScalars ℝ
  have firstSmooth : ContDiffOn ℝ ∞ first domain := outerSmooth output parameter.1 parameter.2.1
  have secondSmooth : ContDiffOn ℝ ∞ second domain :=
    (innerSmooth parameter.1 input parameter.2.2).comp
      (orthogonal parameter.2.1).toContinuousLinearEquiv.contDiff.contDiffOn
      (fun source inside => (invariant parameter.2.1 source).mpr inside)
  refine ⟨composition.isBoundedBilinearMap.contDiff.comp₂_contDiffOn firstSmooth secondSmooth, ?_⟩
  intro rank word point inside
  have allocated := bilinear _ _ _ composition domain openDomain first second firstSmooth secondSmooth
    rank (fun position => spatialDirection (word position)) point inside
  have exactAllocation :
      wordDerivative rank word (composedCoefficient orthogonal outer inner output input parameter) point =
        ∑ selected : Finset (Fin rank),
          allocationTerm orthogonal outer inner output input parameter rank word selected point := by
    change wordDerivative rank word (fun source => composition (first source) (second source)) point = _
    rw [show wordDerivative rank word (fun source => composition (first source) (second source)) point =
      ∑ selected : Finset (Fin rank), composition
        (selectedDerivative (fun position => spatialDirection (word position)) selected first point)
        (selectedDerivative (fun position => spatialDirection (word position)) selectedᶜ second point)
      from allocated]
    apply Finset.sum_congr rfl
    intro selected _
    change (wordDerivative selected.card (subword word selected) first point).comp
      (wordDerivative (selectedᶜ).card (subword word selectedᶜ) second point) = _
    rw [word_chain domain openDomain (orthogonal parameter.2.1) (invariant parameter.2.1)
      (fun source => inner parameter.1 input (parameter.2.2, source)) _ _ point inside]
    rfl
  refine ⟨exactAllocation, exactAllocation.trans ?_⟩
  apply Finset.sum_congr rfl
  intro selected _
  exact allocation_expansion orthogonal outer inner output input parameter rank word selected point

theorem rawData : RawDataGoal := by
  intro Outer Inner _ _ outerMeasure innerMeasure inputDimension middleDimension outputDimension domain outer inner
  exact coefficients Outer Inner inputDimension middleDimension outputDimension domain outer.domainOpen
    outer.orthogonal outer.invariant outer.coefficient inner.coefficient outer.coefficientSmooth inner.coefficientSmooth

theorem canonicalDerivative : CanonicalDerivativeGoal := by
  intro Parameter inputDimension outputDimension coefficient multiindex pair
  rfl

theorem firstOrder : FirstOrderGoal := by
  intro Outer Inner inputDimension middleDimension outputDimension domain openDomain orthogonal invariant
    outer inner outerSmooth innerSmooth output input parameter direction point inside
  let composition := (ContinuousLinearMap.compL ℂ (PhysicalValue inputDimension)
    (PhysicalValue middleDimension) (PhysicalValue outputDimension)).bilinearRestrictScalars ℝ
  have outerLocal := (outerSmooth output parameter.1 parameter.2.1).contDiffAt (openDomain.mem_nhds inside)
  have innerLocal := (innerSmooth parameter.1 input parameter.2.2).contDiffAt
    (openDomain.mem_nhds ((invariant parameter.2.1 point).mpr inside))
  have outerDerivative := (outerLocal.differentiableAt (by simp)).hasFDerivAt
  have innerDerivative := (innerLocal.differentiableAt (by simp)).hasFDerivAt.comp point
    (orthogonal parameter.2.1).toContinuousLinearEquiv.hasFDerivAt
  exact bilinear_derivative composition outerDerivative innerDerivative (spatialDirection direction)

theorem zero : ZeroGoal := by
  refine ⟨?_, ?_, ?_⟩
  · intro Value _ _ function word point
    rfl
  · intro orthogonal word target
    simp [chainFactor_eq]
  · intro Outer Inner inputDimension middleDimension outputDimension orthogonal outer inner output input parameter word point
    constructor
    · rw [Fintype.sum_unique]
      rfl
    · rw [Fintype.sum_unique]
      change (∑ target : Word 0, (1 : ℝ) • composedCoefficient orthogonal outer inner output input parameter point) = _
      simp only [Fintype.sum_unique, one_smul]

theorem block : BlockGoal :=
  ⟨positions, bilinear, chain, coefficients, rawData, canonicalDerivative, firstOrder, zero⟩

end Grad.RepresentedKernel.SpatialProduct
