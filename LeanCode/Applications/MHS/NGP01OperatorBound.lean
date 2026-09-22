import NGP01MixedBound
import P0910HigherExterior

noncomputable section

set_option maxHeartbeats 800000

open Set
open scoped BigOperators

namespace Grad.CartesianState

open Grad.ClosedJets
open Grad.DiskExtension.Operator

local instance ngp01OperatorCellPeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩

local instance ngp01OperatorClosedDiskCompactSpace : CompactSpace ClosedDisk := by
  rw [← isCompact_iff_compactSpace, closedUnitDisk_eq_closedBall]
  exact isCompact_closedBall (0 : SpatialPlane) 1

/-- The order-`r` derivative of a closed disk–cell field, assembled as the
genuine multilinear operator on the Euclidean physical space. -/
def closedPhysicalOperatorDerivative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (order : ℕ) :
    C(DiskCellDomain,
      SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension) where
  toFun point := ∑ word : MixedCartesianWord order,
    (spatialCellWordCoefficient word).smulRight
      (closedMixedDerivative field order word point)
  continuous_toFun := by
    apply continuous_finsetSum
    intro word _
    exact ((ContinuousMultilinearMap.smulRightL ℝ
      (fun _ : Fin order => SpatialCell) (ComplexEuclidean dimension)
      (spatialCellWordCoefficient word)).continuous.comp
        (closedMixedDerivative field order word).continuous)

theorem closedPhysicalOperatorDerivative_norm_le_bound
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ) :
    ‖closedPhysicalOperatorDerivative field order‖ ≤
      closedHigherDerivativeBound field order := by
  rw [ContinuousMap.norm_le _
    (closedHigherDerivativeBound_nonnegative field order)]
  intro point
  change ‖∑ word : MixedCartesianWord order,
      (spatialCellWordCoefficient word).smulRight
        (closedMixedDerivative field order word point)‖ ≤ _
  rw [closedHigherDerivativeBound]
  calc
    ‖∑ word : MixedCartesianWord order,
        (spatialCellWordCoefficient word).smulRight
          (closedMixedDerivative field order word point)‖ ≤
      ∑ word : MixedCartesianWord order,
        ‖(spatialCellWordCoefficient word).smulRight
          (closedMixedDerivative field order word point)‖ := norm_sum_le _ _
    _ ≤ ∑ word : MixedCartesianWord order,
        ‖spatialCellWordCoefficient word‖ *
          ‖closedMixedDerivative field order word‖ := by
      apply Finset.sum_le_sum
      intro word _
      rw [ContinuousMultilinearMap.norm_smulRight]
      exact mul_le_mul_of_nonneg_left
        ((closedMixedDerivative field order word).norm_coe_le_norm point)
        (norm_nonneg _)

/-- The finite coordinate-to-operator comparison constant at one physical
derivative order. -/
def m15OperatorConstant (order : ℕ) : ℝ :=
  (∑ word : MixedCartesianWord order, ‖spatialCellWordCoefficient word‖) *
    m15EvaluationConstant

theorem m15OperatorConstant_nonnegative (order : ℕ) :
    0 ≤ m15OperatorConstant order := by
  exact mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    m15EvaluationConstant_nonneg

/-- The accepted P09 operator derivative bound, quantitatively controlled by
the literal original `A^(j+3)` norm. -/
theorem originalGrade_closedHigherDerivativeBound_le
    {dimension order j : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters dimension (j + 3))
    (orderLe : order ≤ j) :
    closedHigherDerivativeBound
        (weightedSmoothEquiv parameters field.toCore) order ≤
      m15OperatorConstant order * ‖field‖ := by
  rw [closedHigherDerivativeBound, m15OperatorConstant]
  calc
    ∑ word : MixedCartesianWord order,
        ‖spatialCellWordCoefficient word‖ *
          ‖closedMixedDerivative (weightedSmoothEquiv parameters field.toCore)
            order word‖ ≤
      ∑ word : MixedCartesianWord order,
        ‖spatialCellWordCoefficient word‖ *
          (m15EvaluationConstant * ‖field‖) := by
      apply Finset.sum_le_sum
      intro word _
      exact mul_le_mul_of_nonneg_left
        (originalGrade_mixedCoordinateDerivative_bound
          parameters field word orderLe)
        (norm_nonneg _)
    _ = ((∑ word : MixedCartesianWord order,
          ‖spatialCellWordCoefficient word‖) * m15EvaluationConstant) *
        ‖field‖ := by
      rw [← Finset.sum_mul]
      ring

/-- Pointwise Euclidean operator norm of every physical derivative of order
at most `j`, with the exact three-grade loss. -/
theorem originalGrade_operatorDerivative_point_bound
    {dimension order j : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters dimension (j + 3))
    (orderLe : order ≤ j) (point : SpatialCell) :
    ‖closedHigherDerivative (order := order)
        (weightedSmoothEquiv parameters field.toCore) point‖ ≤
      m15OperatorConstant order * ‖field‖ := by
  exact (closedHigherDerivative_norm_le_bound
      (weightedSmoothEquiv parameters field.toCore) order point).trans
    (originalGrade_closedHigherDerivativeBound_le
      parameters field orderLe)

/-- One common constant controlling all Euclidean operator derivatives from
order zero through `j`. -/
def physicalEvaluationConstant (j : ℕ) : ℝ :=
  ∑ order ∈ Finset.range (j + 1), m15OperatorConstant order

theorem physicalEvaluationConstant_nonnegative (j : ℕ) :
    0 ≤ physicalEvaluationConstant j := by
  exact Finset.sum_nonneg fun order _ => m15OperatorConstant_nonnegative order

theorem m15OperatorConstant_le_physicalEvaluationConstant
    {order j : ℕ} (orderLe : order ≤ j) :
    m15OperatorConstant order ≤ physicalEvaluationConstant j := by
  unfold physicalEvaluationConstant
  exact Finset.single_le_sum
    (fun candidate _ => m15OperatorConstant_nonnegative candidate)
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr orderLe))

/-- Uniform pointwise form of the exact physical `C^j` estimate.  Its left
side is the genuine P09 Euclidean multilinear-operator norm. -/
theorem originalGrade_all_operatorDerivatives_point_bound
    {dimension order j : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters dimension (j + 3))
    (orderLe : order ≤ j) (point : SpatialCell) :
    ‖closedHigherDerivative (order := order)
        (weightedSmoothEquiv parameters field.toCore) point‖ ≤
      physicalEvaluationConstant j * ‖field‖ := by
  exact (originalGrade_operatorDerivative_point_bound
      parameters field orderLe point).trans
    (mul_le_mul_of_nonneg_right
      (m15OperatorConstant_le_physicalEvaluationConstant orderLe)
      (norm_nonneg field))

/-- The finite collection whose maximum is the exact closed physical `C^j`
norm. -/
def physicalDerivativeNorms {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (j : ℕ) : Finset ℝ :=
  Finset.univ.image (fun order : Fin (j + 1) =>
    ‖closedPhysicalOperatorDerivative field order.val‖)

theorem physicalDerivativeNorms_nonempty {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (j : ℕ) :
    (physicalDerivativeNorms field j).Nonempty := by
  exact Finset.univ_nonempty.image _

/-- The literal D01/GB1 physical norm: the maximum of the closed-cell
supremum operator norms at every derivative order `0,…,j`. -/
def closedPhysicalCNorm {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (j : ℕ) : ℝ :=
  (physicalDerivativeNorms field j).max'
    (physicalDerivativeNorms_nonempty field j)

theorem closedPhysicalOperatorDerivative_norm_le_cNorm
    {dimension order j : ℕ} (field : DiskCellClosedJet dimension)
    (orderLe : order ≤ j) :
    ‖closedPhysicalOperatorDerivative field order‖ ≤
      closedPhysicalCNorm field j := by
  unfold closedPhysicalCNorm
  apply Finset.le_max'
  rw [physicalDerivativeNorms, Finset.mem_image]
  exact ⟨⟨order, Nat.lt_succ_iff.mpr orderLe⟩, Finset.mem_univ _, rfl⟩

/-- Exact `C^j` evaluation bound at the original analytic width and the
literal loss of three grades. -/
theorem originalGrade_closedPhysicalCNorm_bound
    {dimension j : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters dimension (j + 3)) :
    closedPhysicalCNorm (weightedSmoothEquiv parameters field.toCore) j ≤
      physicalEvaluationConstant j * ‖field‖ := by
  unfold closedPhysicalCNorm
  rw [Finset.max'_le_iff]
  intro value valueMembership
  rw [physicalDerivativeNorms, Finset.mem_image] at valueMembership
  obtain ⟨order, _, rfl⟩ := valueMembership
  exact (closedPhysicalOperatorDerivative_norm_le_bound
      (weightedSmoothEquiv parameters field.toCore) order.val).trans
    ((originalGrade_closedHigherDerivativeBound_le
      parameters field (Nat.lt_succ_iff.mp order.isLt)).trans
      (mul_le_mul_of_nonneg_right
        (m15OperatorConstant_le_physicalEvaluationConstant
          (Nat.lt_succ_iff.mp order.isLt))
        (norm_nonneg field)))

end Grad.CartesianState
