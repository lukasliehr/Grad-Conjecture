import GC13Smooth
import SP1Consumers

noncomputable section

set_option maxHeartbeats 5000000

open Set
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.RepresentedKernel.SpatialProduct
open Grad.WeakTesting.Commutation
open scoped BigOperators ContDiff Topology

namespace Grad.GaugeCoefficients.Radial

open Grad.GaugeCoefficients.Algebra

def orthogonalClosedPoint (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (point : ClosedDisk) : ClosedDisk :=
  ⟨orthogonal point.val, by
    change ‖orthogonal point.val‖ ≤ 1
    rw [orthogonal.norm_map]
    exact point.property⟩

theorem continuous_orthogonalClosedPoint
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) :
    Continuous (orthogonalClosedPoint orthogonal) := by
  exact (orthogonal.continuous.comp continuous_subtype_val).subtype_mk _

theorem openUnitDisk_invariant
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) :
    Grad.KernelPullback.Domain.Invariant openUnitDisk orthogonal := by
  intro point
  change ‖orthogonal point‖ < 1 ↔ ‖point‖ < 1
  rw [orthogonal.norm_map]

def orthogonalJetValue {inputDimension outputDimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (field : SmoothOperatorJet inputDimension outputDimension) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) where
  toFun point := field.value (orthogonalClosedPoint orthogonal point)
  continuous_toFun := field.value.continuous.comp
    (continuous_orthogonalClosedPoint orthogonal)

theorem closedDiskLift_orthogonalJetValue
    {inputDimension outputDimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (field : SmoothOperatorJet inputDimension outputDimension) :
    closedDiskLift (orthogonalJetValue orthogonal field) =
      fun point => closedDiskLift field.value (orthogonal point) := by
  funext point
  by_cases inside : point ∈ closedUnitDisk
  · have imageInside : orthogonal point ∈ closedUnitDisk := by
      change ‖orthogonal point‖ ≤ 1
      rw [orthogonal.norm_map]
      exact inside
    simp [closedDiskLift, orthogonalJetValue, inside, imageInside]
    rfl
  · have imageOutside : orthogonal point ∉ closedUnitDisk := by
      intro imageInside
      apply inside
      change ‖point‖ ≤ 1
      rw [← orthogonal.norm_map]
      exact imageInside
    simp [closedDiskLift, inside, imageOutside]

def orthogonalTargetIndex {rank : ℕ} (target : Word rank) :
    CartesianMultiIndex :=
  (directionCount target 0, directionCount target 1)

theorem wordDerivative_eq_smoothOperatorDerivative
    {inputDimension outputDimension rank : ℕ}
    (field : SmoothOperatorJet inputDimension outputDimension)
    (target : Word rank) (point : SpatialPlane) (inside : point ∈ openUnitDisk) :
    wordDerivative rank target (closedDiskLift field.value) point =
      smoothOperatorDerivative field (orthogonalTargetIndex target)
        ⟨point, openDiskMembershipClosed point inside⟩ := by
  generalize zeroEquality : directionCount target 0 = zeros
  generalize oneEquality : directionCount target 1 = ones
  have cardinality : zeros + ones = rank := by
    rw [← zeroEquality, ← oneEquality]
    exact count_total rank target
  subst rank
  have canonical := wordDerivative_canonical openUnitDisk_isOpen zeros ones target
    zeroEquality oneEquality field.smoothInterior (x := point) inside
  rw [canonical]
  unfold orthogonalTargetIndex
  rw [zeroEquality, oneEquality]
  change cartesianMultiDerivative (zeros, ones) (closedDiskLift field.value) point =
    (Classical.choose (field.derivativeExists (zeros, ones)))
      ⟨point, openDiskMembershipClosed point inside⟩
  exact (Classical.choose_spec
    (field.derivativeExists (zeros, ones))
      ⟨point, openDiskMembershipClosed point inside⟩ inside).symm

def orthogonalDerivativeTerm
    {inputDimension outputDimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (field : SmoothOperatorJet inputDimension outputDimension)
    (index : CartesianMultiIndex) (target : Word (cartesianOrder index)) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) where
  toFun point :=
    (chainFactor (cartesianOrder index) orthogonal
      (cartesianMultiIndexWord index) target : ℂ) •
        smoothOperatorDerivative field (orthogonalTargetIndex target)
          (orthogonalClosedPoint orthogonal point)
  continuous_toFun := by
    exact (continuous_const : Continuous fun _ : ClosedDisk =>
      (chainFactor (cartesianOrder index) orthogonal
        (cartesianMultiIndexWord index) target : ℂ)).smul
      ((smoothOperatorDerivative field (orthogonalTargetIndex target)).continuous.comp
        (continuous_orthogonalClosedPoint orthogonal))

def orthogonalDerivativeExtension
    {inputDimension outputDimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (field : SmoothOperatorJet inputDimension outputDimension)
    (index : CartesianMultiIndex) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) where
  toFun point := ∑ target : Word (cartesianOrder index),
    orthogonalDerivativeTerm orthogonal field index target point
  continuous_toFun := by
    apply continuous_finsetSum
    intro target _membership
    exact (orthogonalDerivativeTerm orthogonal field index target).continuous

theorem orthogonalDerivativeExtension_spec
    {inputDimension outputDimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (field : SmoothOperatorJet inputDimension outputDimension)
    (index : CartesianMultiIndex) :
    IsOperatorDerivativeExtension (orthogonalJetValue orthogonal field) index
      (orthogonalDerivativeExtension orthogonal field index) := by
  intro point inside
  have imageInside : orthogonal point.val ∈ openUnitDisk :=
    (openUnitDisk_invariant orthogonal point.val).mpr inside
  simp only [orthogonalDerivativeExtension, orthogonalDerivativeTerm]
  change (∑ target : Word (cartesianOrder index),
      (chainFactor (cartesianOrder index) orthogonal
        (cartesianMultiIndexWord index) target : ℂ) •
        smoothOperatorDerivative field (orthogonalTargetIndex target)
          (orthogonalClosedPoint orthogonal point)) = _
  rw [closedDiskLift_orthogonalJetValue]
  change _ = wordDerivative (cartesianOrder index)
    (cartesianMultiIndexWord index)
      (fun source => closedDiskLift field.value (orthogonal source)) point.val
  rw [word_chain openUnitDisk openUnitDisk_isOpen orthogonal
    (openUnitDisk_invariant orthogonal) (closedDiskLift field.value)
    (cartesianOrder index) (cartesianMultiIndexWord index) point.val inside]
  rw [twisted_expansion]
  apply Finset.sum_congr rfl
  intro target _membership
  rw [wordDerivative_eq_smoothOperatorDerivative field target
    (orthogonal point.val) imageInside]
  change ((chainFactor (cartesianOrder index) orthogonal
      (cartesianMultiIndexWord index) target : ℂ) •
        smoothOperatorDerivative field (orthogonalTargetIndex target)
          (orthogonalClosedPoint orthogonal point)) =
    chainFactor (cartesianOrder index) orthogonal
      (cartesianMultiIndexWord index) target •
        smoothOperatorDerivative field (orthogonalTargetIndex target)
          ⟨orthogonal point.val, openDiskMembershipClosed _ imageInside⟩
  congr 1

def orthogonalSmoothOperatorJet
    {inputDimension outputDimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (field : SmoothOperatorJet inputDimension outputDimension) :
    SmoothOperatorJet inputDimension outputDimension where
  value := orthogonalJetValue orthogonal field
  smoothInterior := by
    rw [closedDiskLift_orthogonalJetValue]
    exact field.smoothInterior.comp orthogonal.contDiff.contDiffOn
      (fun point inside => (openUnitDisk_invariant orthogonal point).mpr inside)
  derivativeExists := fun index =>
    ⟨orthogonalDerivativeExtension orthogonal field index,
      orthogonalDerivativeExtension_spec orthogonal field index⟩

theorem orthogonalSmoothOperatorJet_derivative
    {inputDimension outputDimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (field : SmoothOperatorJet inputDimension outputDimension)
    (index : CartesianMultiIndex) :
    smoothOperatorDerivative (orthogonalSmoothOperatorJet orthogonal field) index =
      orthogonalDerivativeExtension orthogonal field index := by
  exact smoothOperatorDerivative_eq_of_spec _ _ _
    (orthogonalDerivativeExtension_spec orthogonal field index)

theorem orthogonalSmoothOperatorJet_derivative_index
    {grade inputDimension outputDimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (field : SmoothOperatorJet inputDimension outputDimension)
    (index : DerivativeIndex grade) :
    smoothOperatorDerivative (orthogonalSmoothOperatorJet orthogonal field)
        (derivativeMultiIndex index) =
      ∑ target : Word (derivativeOrder index),
        orthogonalDerivativeTerm orthogonal field (derivativeMultiIndex index) target := by
  rw [orthogonalSmoothOperatorJet_derivative]
  apply ContinuousMap.ext
  intro point
  simp [orthogonalDerivativeExtension, derivativeOrder, derivativeMultiIndex,
    cartesianOrder]
  let evaluation : ContinuousMap ClosedDisk
      (OperatorValue inputDimension outputDimension) →+
        OperatorValue inputDimension outputDimension :=
    { toFun := fun function => function point
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change (∑ target, evaluation
      (orthogonalDerivativeTerm orthogonal field
        ((index.1.1 : ℕ), (index.1.2 : ℕ)) target)) =
    evaluation (∑ target, orthogonalDerivativeTerm orthogonal field
      ((index.1.1 : ℕ), (index.1.2 : ℕ)) target)
  exact (map_sum evaluation (fun target => orthogonalDerivativeTerm orthogonal field
    ((index.1.1 : ℕ), (index.1.2 : ℕ)) target) Finset.univ).symm

theorem orthogonalSmoothOperatorJet_derivative_index_apply
    {grade inputDimension outputDimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (field : SmoothOperatorJet inputDimension outputDimension)
    (index : DerivativeIndex grade) (point : ClosedDisk) :
    smoothOperatorDerivative (orthogonalSmoothOperatorJet orthogonal field)
        (derivativeMultiIndex index) point =
      ∑ target : Word (derivativeOrder index),
        orthogonalDerivativeTerm orthogonal field (derivativeMultiIndex index)
          target point := by
  rw [orthogonalSmoothOperatorJet_derivative]
  rfl

end Grad.GaugeCoefficients.Radial
