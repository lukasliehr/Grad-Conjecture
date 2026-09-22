import GC10Combinatorics

noncomputable section

set_option maxHeartbeats 3000000

open Set
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope
open Grad.RepresentedKernel.SpatialProduct
open Grad.WeakTesting.Commutation
open scoped BigOperators ContDiff ENNReal Topology

namespace Grad.GaugeCoefficients.Algebra

/-- The same Cartesian multi-index, regarded at its own total grade. -/
def topDerivativeIndex (index : CartesianMultiIndex) :
    DerivativeIndex (cartesianOrder index) := by
  refine ⟨(⟨index.1, by simp [cartesianOrder]⟩,
    ⟨index.2, by simp [cartesianOrder]⟩), ?_⟩
  simp [cartesianOrder]

theorem derivativeMultiIndex_top (index : CartesianMultiIndex) :
    derivativeMultiIndex (topDerivativeIndex index) = index := rfl

def operatorCompositionBilinear (inputDimension middleDimension outputDimension : ℕ) :
    OperatorValue middleDimension outputDimension →L[ℝ]
      OperatorValue inputDimension middleDimension →L[ℝ]
        OperatorValue inputDimension outputDimension :=
  (ContinuousLinearMap.compL ℂ (PhysicalValue inputDimension)
    (PhysicalValue middleDimension) (PhysicalValue outputDimension)).bilinearRestrictScalars ℝ

def smoothOperatorComposeValue
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : SmoothOperatorJet middleDimension outputDimension)
    (inner : SmoothOperatorJet inputDimension middleDimension) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) :=
  continuousOperatorComposition outer.value inner.value

theorem closedDiskLift_smoothOperatorComposeValue
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : SmoothOperatorJet middleDimension outputDimension)
    (inner : SmoothOperatorJet inputDimension middleDimension) :
    closedDiskLift (smoothOperatorComposeValue outer inner) =
      fun point => (closedDiskLift outer.value point).comp
        (closedDiskLift inner.value point) := by
  funext point
  by_cases inside : point ∈ closedUnitDisk
  · unfold closedDiskLift
    simp only [dif_pos inside]
    rfl
  · unfold closedDiskLift
    simp only [dif_neg inside]
    rfl

def smoothOperatorComposeDerivative
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : SmoothOperatorJet middleDimension outputDimension)
    (inner : SmoothOperatorJet inputDimension middleDimension)
    (index : CartesianMultiIndex) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) :=
  let top := topDerivativeIndex index
  ∑ split : DerivativeSplit top,
    (splitMultiplicity top split : ℂ) •
      continuousOperatorComposition
        (smoothOperatorDerivative outer
          (derivativeMultiIndex (lowerDerivativeIndex top split)))
        (smoothOperatorDerivative inner
          (derivativeMultiIndex (upperDerivativeIndex top split)))

theorem selectedDerivative_eq_smoothOperatorDerivative
    {inputDimension outputDimension : ℕ}
    (field : SmoothOperatorJet inputDimension outputDimension)
    (index : CartesianMultiIndex)
    (selected : Finset (Fin (cartesianOrder index)))
    (point : ClosedDisk) (inside : point.val ∈ openUnitDisk) :
    selectedDerivative
        (fun position => spatialBasis (cartesianMultiIndexWord index position)) selected
        (closedDiskLift field.value) point.val =
      smoothOperatorDerivative field
        (derivativeMultiIndex
          (lowerDerivativeIndex (topDerivativeIndex index)
            (selectionDerivativeSplit (topDerivativeIndex index) selected))) point := by
  let word := selectedCartesianSubword index selected
  have canonical := wordDerivative_cartesianMultiDerivative
    openUnitDisk_isOpen selected.card word (closedDiskLift field.value)
    field.smoothInterior point.val inside
  change wordDerivative selected.card word (closedDiskLift field.value) point.val = _
  rw [selectedCartesianSubword_zero_count,
    selectedCartesianSubword_one_count] at canonical
  exact canonical.trans (Classical.choose_spec
    (field.derivativeExists
      (derivativeMultiIndex
        (lowerDerivativeIndex (topDerivativeIndex index)
          (selectionDerivativeSplit (topDerivativeIndex index) selected)))) point inside).symm

theorem selectedComplementDerivative_eq_smoothOperatorDerivative
    {inputDimension outputDimension : ℕ}
    (field : SmoothOperatorJet inputDimension outputDimension)
    (index : CartesianMultiIndex)
    (selected : Finset (Fin (cartesianOrder index)))
    (point : ClosedDisk) (inside : point.val ∈ openUnitDisk) :
    selectedDerivative
        (fun position => spatialBasis (cartesianMultiIndexWord index position)) selectedᶜ
        (closedDiskLift field.value) point.val =
      smoothOperatorDerivative field
        (derivativeMultiIndex
          (upperDerivativeIndex (topDerivativeIndex index)
            (selectionDerivativeSplit (topDerivativeIndex index) selected))) point := by
  let word := selectedCartesianSubword index selectedᶜ
  have canonical := wordDerivative_cartesianMultiDerivative
    openUnitDisk_isOpen selectedᶜ.card word (closedDiskLift field.value)
    field.smoothInterior point.val inside
  change wordDerivative selectedᶜ.card word (closedDiskLift field.value) point.val = _
  dsimp [word] at canonical
  have zeroCount :
      directionCount (selectedCartesianSubword index selectedᶜ) 0 =
        (upperDerivativeIndex (topDerivativeIndex index)
          (selectionDerivativeSplit (topDerivativeIndex index) selected)).1.1 := by
    convert selectedCartesianSubword_compl_zero_count
      (topDerivativeIndex index) selected using 1
    all_goals simp only [derivativeMultiIndex_top]
    all_goals rfl
  have oneCount :
      directionCount (selectedCartesianSubword index selectedᶜ) 1 =
        (upperDerivativeIndex (topDerivativeIndex index)
          (selectionDerivativeSplit (topDerivativeIndex index) selected)).1.2 := by
    convert selectedCartesianSubword_compl_one_count
      (topDerivativeIndex index) selected using 1
    all_goals simp only [derivativeMultiIndex_top]
    all_goals rfl
  rw [zeroCount, oneCount] at canonical
  exact canonical.trans (Classical.choose_spec
    (field.derivativeExists
      (derivativeMultiIndex
        (upperDerivativeIndex (topDerivativeIndex index)
          (selectionDerivativeSplit (topDerivativeIndex index) selected)))) point inside).symm

theorem smoothOperatorComposeDerivative_spec
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : SmoothOperatorJet middleDimension outputDimension)
    (inner : SmoothOperatorJet inputDimension middleDimension)
    (index : CartesianMultiIndex) :
    IsOperatorDerivativeExtension (smoothOperatorComposeValue outer inner) index
      (smoothOperatorComposeDerivative outer inner index) := by
  intro point inside
  let directions : Fin (cartesianOrder index) → Spatial :=
    fun position => spatialBasis (cartesianMultiIndexWord index position)
  have allocated := bilinear _ _ _
    (operatorCompositionBilinear inputDimension middleDimension outputDimension)
    openUnitDisk openUnitDisk_isOpen
    (closedDiskLift outer.value) (closedDiskLift inner.value)
    outer.smoothInterior inner.smoothInterior
    (cartesianOrder index) directions point.val inside
  have productDerivative :
      cartesianMultiDerivative index
          (fun source => (closedDiskLift outer.value source).comp
            (closedDiskLift inner.value source)) point.val =
        ∑ selected : Finset (Fin (cartesianOrder index)),
          (smoothOperatorDerivative outer
            (derivativeMultiIndex
              (lowerDerivativeIndex (topDerivativeIndex index)
                (selectionDerivativeSplit (topDerivativeIndex index) selected))) point).comp
          (smoothOperatorDerivative inner
            (derivativeMultiIndex
              (upperDerivativeIndex (topDerivativeIndex index)
                (selectionDerivativeSplit (topDerivativeIndex index) selected))) point) := by
    change wordDerivative (cartesianOrder index) (cartesianMultiIndexWord index)
        (fun source => (closedDiskLift outer.value source).comp
          (closedDiskLift inner.value source)) point.val = _
    rw [show wordDerivative (cartesianOrder index) (cartesianMultiIndexWord index)
        (fun source => (closedDiskLift outer.value source).comp
          (closedDiskLift inner.value source)) point.val =
        ∑ selected : Finset (Fin (cartesianOrder index)),
          operatorCompositionBilinear inputDimension middleDimension outputDimension
            (selectedDerivative directions selected (closedDiskLift outer.value) point.val)
            (selectedDerivative directions selectedᶜ (closedDiskLift inner.value) point.val)
      from allocated]
    apply Finset.sum_congr rfl
    intro selected _membership
    rw [selectedDerivative_eq_smoothOperatorDerivative outer index selected point inside,
      selectedComplementDerivative_eq_smoothOperatorDerivative inner index selected point inside]
    rfl
  rw [closedDiskLift_smoothOperatorComposeValue]
  rw [productDerivative]
  simp only [smoothOperatorComposeDerivative]
  symm
  have grouped :
      (∑ selected : Finset (Fin (cartesianOrder index)),
        (smoothOperatorDerivative outer
          (derivativeMultiIndex
            (lowerDerivativeIndex (topDerivativeIndex index)
              (selectionDerivativeSplit (topDerivativeIndex index) selected))) point).comp
        (smoothOperatorDerivative inner
          (derivativeMultiIndex
            (upperDerivativeIndex (topDerivativeIndex index)
              (selectionDerivativeSplit (topDerivativeIndex index) selected))) point)) =
      ∑ split : DerivativeSplit (topDerivativeIndex index),
        splitMultiplicity (topDerivativeIndex index) split •
          (smoothOperatorDerivative outer
            (derivativeMultiIndex
              (lowerDerivativeIndex (topDerivativeIndex index) split)) point).comp
          (smoothOperatorDerivative inner
            (derivativeMultiIndex
              (upperDerivativeIndex (topDerivativeIndex index) split)) point) := by
    convert sum_selectionDerivativeSplit (topDerivativeIndex index)
      (fun split =>
        (smoothOperatorDerivative outer
          (derivativeMultiIndex
            (lowerDerivativeIndex (topDerivativeIndex index) split)) point).comp
        (smoothOperatorDerivative inner
          (derivativeMultiIndex
            (upperDerivativeIndex (topDerivativeIndex index) split)) point)) using 1
    all_goals simp only [derivativeMultiIndex_top]
    all_goals rfl
  rw [grouped]
  let maps := fun split : DerivativeSplit (topDerivativeIndex index) =>
    (splitMultiplicity (topDerivativeIndex index) split : ℂ) •
      continuousOperatorComposition
        (smoothOperatorDerivative outer
          (derivativeMultiIndex
            (lowerDerivativeIndex (topDerivativeIndex index) split)))
        (smoothOperatorDerivative inner
          (derivativeMultiIndex
            (upperDerivativeIndex (topDerivativeIndex index) split)))
  let evaluation :
      ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) →+
        OperatorValue inputDimension outputDimension := {
    toFun function := function point
    map_zero' := rfl
    map_add' _ _ := rfl }
  have evaluation_sum :
      (∑ split, maps split) point = ∑ split, maps split point := by
    change evaluation (∑ split, maps split) =
      ∑ split, evaluation (maps split)
    rw [map_sum]
  rw [evaluation_sum]
  apply Finset.sum_congr rfl
  intro split _membership
  change splitMultiplicity (topDerivativeIndex index) split •
      (smoothOperatorDerivative outer
        (derivativeMultiIndex
          (lowerDerivativeIndex (topDerivativeIndex index) split)) point).comp
      (smoothOperatorDerivative inner
        (derivativeMultiIndex
          (upperDerivativeIndex (topDerivativeIndex index) split)) point) =
    (splitMultiplicity (topDerivativeIndex index) split : ℂ) •
      (smoothOperatorDerivative outer
        (derivativeMultiIndex
          (lowerDerivativeIndex (topDerivativeIndex index) split)) point).comp
      (smoothOperatorDerivative inner
        (derivativeMultiIndex
          (upperDerivativeIndex (topDerivativeIndex index) split)) point)
  exact (Nat.cast_smul_eq_nsmul ℂ
    (splitMultiplicity (topDerivativeIndex index) split)
    ((smoothOperatorDerivative outer
      (derivativeMultiIndex
        (lowerDerivativeIndex (topDerivativeIndex index) split)) point).comp
    (smoothOperatorDerivative inner
      (derivativeMultiIndex
        (upperDerivativeIndex (topDerivativeIndex index) split)) point))).symm

def smoothOperatorCompose
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : SmoothOperatorJet middleDimension outputDimension)
    (inner : SmoothOperatorJet inputDimension middleDimension) :
    SmoothOperatorJet inputDimension outputDimension where
  value := smoothOperatorComposeValue outer inner
  smoothInterior := by
    rw [closedDiskLift_smoothOperatorComposeValue]
    let composition :=
      operatorCompositionBilinear inputDimension middleDimension outputDimension
    exact composition.isBoundedBilinearMap.contDiff.comp₂_contDiffOn
        outer.smoothInterior inner.smoothInterior
  derivativeExists := fun index =>
    ⟨smoothOperatorComposeDerivative outer inner index,
      smoothOperatorComposeDerivative_spec outer inner index⟩

theorem smoothOperatorCompose_derivative
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : SmoothOperatorJet middleDimension outputDimension)
    (inner : SmoothOperatorJet inputDimension middleDimension)
    (index : CartesianMultiIndex) :
    smoothOperatorDerivative (smoothOperatorCompose outer inner) index =
      smoothOperatorComposeDerivative outer inner index := by
  apply continuousMap_eq_of_openDisk
  intro point inside
  unfold smoothOperatorDerivative
  rw [Classical.choose_spec
    ((smoothOperatorCompose outer inner).derivativeExists index) point inside,
    smoothOperatorComposeDerivative_spec outer inner index point inside]
  rfl

end Grad.GaugeCoefficients.Algebra
