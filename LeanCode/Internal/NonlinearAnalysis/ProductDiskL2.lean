import ProductLastFactor

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.CartesianState

def scalarNormLp {Source Value : Type} [MeasurableSpace Source]
    [NormedAddCommGroup Value] {measure : Measure Source} (field : Lp Value 2 measure) :
    Lp ℝ 2 measure :=
  (Lp.memLp field).norm.toLp (fun point => ‖field point‖)

theorem scalarNormLp_ae {Source Value : Type} [MeasurableSpace Source]
    [NormedAddCommGroup Value] {measure : Measure Source} (field : Lp Value 2 measure) :
    ∀ᵐ point ∂measure, scalarNormLp field point = ‖field point‖ :=
  (Lp.memLp field).norm.coeFn_toLp

theorem scalarNormLp_norm {Source Value : Type} [MeasurableSpace Source]
    [NormedAddCommGroup Value] {measure : Measure Source} (field : Lp Value 2 measure) :
    ‖scalarNormLp field‖ = ‖field‖ := by
  apply le_antisymm <;> apply Lp.norm_le_norm_of_ae_le
  · filter_upwards [scalarNormLp_ae field] with point equality
    simp only [equality, norm_norm, le_refl]
  · filter_upwards [scalarNormLp_ae field] with point equality
    simp only [equality, norm_norm, le_refl]

theorem lp_finsetSum_ae {Index Source Value : Type} [MeasurableSpace Source]
    [NormedAddCommGroup Value] {measure : Measure Source}
    (indices : Finset Index) (fields : Index → Lp Value 2 measure) :
    ∀ᵐ point ∂measure, (∑ index ∈ indices, fields index) point =
      ∑ index ∈ indices, fields index point := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact Lp.coeFn_zero _ _ _
  | @insert index indices outside inductionHypothesis =>
    simp only [Finset.sum_insert outside]
    filter_upwards [Lp.coeFn_add (fields index) (∑ other ∈ indices, fields other),
      inductionHypothesis] with point additive sumEquality
    exact additive.trans (congrArg (fun value => fields index point + value) sumEquality)

theorem lp_norm_le_finite_norm_majorant {Index Source First : Type} {Second : Index → Type}
    [Fintype Index] [MeasurableSpace Source]
    [NormedAddCommGroup First] [∀ index, NormedAddCommGroup (Second index)]
    {measure : Measure Source} (field : Lp First 2 measure) (majorants : (index : Index) → Lp (Second index) 2 measure)
    (coefficients : Index → ℝ) (nonnegative : ∀ index, 0 ≤ coefficients index)
    (dominated : ∀ᵐ point ∂measure,
      ‖field point‖ ≤ ∑ index, coefficients index * ‖majorants index point‖) :
    ‖field‖ ≤ ∑ index, coefficients index * ‖majorants index‖ := by
  let terms : Index → Lp ℝ 2 measure := fun index => coefficients index • scalarNormLp (majorants index)
  have termsValue (index : Index) : ∀ᵐ point ∂measure,
      terms index point = coefficients index * ‖majorants index point‖ := by
    filter_upwards [Lp.coeFn_smul (coefficients index) (scalarNormLp (majorants index)),
      scalarNormLp_ae (majorants index)] with point scaled normalized
    exact scaled.trans (congrArg (fun value => coefficients index * value) normalized)
  calc
    _ ≤ ‖∑ index, terms index‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [dominated, lp_finsetSum_ae Finset.univ terms,
        ae_all_iff.mpr termsValue] with point pointBound sumValue eachValue
      rw [sumValue]
      simp only [eachValue]
      rw [Real.norm_of_nonneg (Finset.sum_nonneg
        (fun index _ => mul_nonneg (nonnegative index) (norm_nonneg _)))]
      exact pointBound
    _ ≤ ∑ index, ‖terms index‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro index _
      rw [norm_smul, Real.norm_of_nonneg (nonnegative index), scalarNormLp_norm]

theorem closedDiskL2_norm_le_finite_majorant {Index : Type} [Fintype Index]
    {firstDimension secondDimension : ℕ}
    (field : C(ClosedDisk, ComplexEuclidean firstDimension))
    (majorants : Index → C(ClosedDisk, ComplexEuclidean secondDimension))
    (coefficients : Index → ℝ) (nonnegative : ∀ index, 0 ≤ coefficients index)
    (dominated : ∀ point : ClosedDisk,
      ‖field point‖ ≤ ∑ index, coefficients index * ‖majorants index point‖) :
    ‖closedContinuousToDiskL2 field‖ ≤
      ∑ index, coefficients index * ‖closedContinuousToDiskL2 (majorants index)‖ := by
  apply lp_norm_le_finite_norm_majorant _ _ coefficients nonnegative
  filter_upwards [closedContinuousToDiskL2_ae field,
    ae_all_iff.mpr (fun index => closedContinuousToDiskL2_ae (majorants index)),
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point fieldValue eachValue pointIn
  rw [fieldValue]
  simp only [eachValue]
  simpa only [closedDiskLift, openDiskMembershipClosed point pointIn, dite_true] using
    dominated ⟨point, openDiskMembershipClosed point pointIn⟩

theorem closedMapMemL2 {Value : Type} [NormedAddCommGroup Value]
    (field : C(ClosedDisk, Value)) :
    MemLp (fun point => field (ambientClosedDisk point)) 2 (volume.restrict openUnitDisk) := by
  apply MemLp.of_bound
    ((field.continuous.comp continuous_ambientClosedDisk).aestronglyMeasurable) ‖field‖
  exact Filter.Eventually.of_forall (fun point => ContinuousMap.norm_coe_le_norm field (ambientClosedDisk point))

def closedMapL2 {Value : Type} [NormedAddCommGroup Value] (field : C(ClosedDisk, Value)) :
    Lp Value 2 (volume.restrict openUnitDisk) :=
  (closedMapMemL2 field).toLp (fun point => field (ambientClosedDisk point))

theorem closedMapL2_ae {Value : Type} [NormedAddCommGroup Value] (field : C(ClosedDisk, Value)) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, closedMapL2 field point = field (ambientClosedDisk point) :=
  (closedMapMemL2 field).coeFn_toLp

theorem closedMapL2_eq_original {dimension : ℕ} (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    closedMapL2 field = closedContinuousToDiskL2 field := by
  apply Lp.ext
  filter_upwards [closedMapL2_ae field, closedContinuousToDiskL2_ae field,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point generic original pointIn
  rw [generic, original]
  simp only [closedDiskLift, openDiskMembershipClosed point pointIn, dite_true]
  congr 1
  apply Subtype.ext
  exact ambientClosedDisk_val_of_mem (openDiskMembershipClosed point pointIn)

theorem closedMapL2_norm_le_finite_majorant {Index First : Type} {Second : Index → Type} [Fintype Index]
    [NormedAddCommGroup First] [∀ index, NormedAddCommGroup (Second index)]
    (field : C(ClosedDisk, First)) (majorants : (index : Index) → C(ClosedDisk, Second index))
    (coefficients : Index → ℝ) (nonnegative : ∀ index, 0 ≤ coefficients index)
    (dominated : ∀ point : ClosedDisk,
      ‖field point‖ ≤ ∑ index, coefficients index * ‖majorants index point‖) :
    ‖closedMapL2 field‖ ≤ ∑ index, coefficients index * ‖closedMapL2 (majorants index)‖ := by
  apply lp_norm_le_finite_norm_majorant _ _ coefficients nonnegative
  filter_upwards [closedMapL2_ae field, ae_all_iff.mpr (fun index => closedMapL2_ae (majorants index))]
    with point fieldValue eachValue
  rw [fieldValue]
  simp only [eachValue]
  exact dominated (ambientClosedDisk point)

theorem jetOperatorDerivative_L2_bound {dimension order : ℕ} (field : ClosedJet dimension) :
    ‖closedMapL2 (jetOperatorDerivative order field)‖ ≤
      ∑ word : CartesianWord order, ‖spatialPlaneWordCoefficient word‖ *
        ‖closedContinuousToDiskL2 (closedDerivative field order word)‖ := by
  simpa only [closedMapL2_eq_original] using closedMapL2_norm_le_finite_majorant
    (jetOperatorDerivative order field) (fun word => closedDerivative field order word)
    (fun word => ‖spatialPlaneWordCoefficient word‖) (fun _ => norm_nonneg _)
    (jetOperatorDerivative_point_bound field)

end Grad.NonlinearProduct
