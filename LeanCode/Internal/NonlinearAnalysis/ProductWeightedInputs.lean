import ProductDerivativeAllocation
import NGP01CoordinateBound

noncomputable section

set_option maxHeartbeats 700000

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal Topology

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.CartesianState Grad.Constraints

local instance productClosedDiskCompact : CompactSpace ClosedDisk := by
  rw [← isCompact_iff_compactSpace, closedUnitDisk_eq_closedBall]
  exact isCompact_closedBall (0 : SpatialPlane) 1

theorem weighted_ordinaryGrade_norm {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) :
    ‖ordinaryGradeCoordinates grade (weightedCoefficientCoreEquiv parameters field)‖ =
      originalGradeNorm grade field := by
  rw [ordinaryGradeCoordinates_weighted_norm]
  unfold originalGradeNorm
  rw [gradeCore_norm_eq_cartesianGradeSeminorm,
    cartesianGradeSeminorm_apply, gradeCoreCoordinates_apply]
  rfl

/-- The first p-1 factors' exact disk supremum and outer l1 estimate. -/
theorem weighted_word_sup_summable {dimension order : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (word : CartesianWord order) (power : ℕ) :
    Summable (fun cell : ℤ => cellFrequency cell ^ power *
      ‖closedDerivative (phaseWeightedJet parameters cell (field.val cell)) order word‖) :=
  m15_frequencyWeighted_sup_summable (weightedCoefficientCoreEquiv parameters field) word power

theorem weighted_word_sup_tsum_bound {dimension order : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (word : CartesianWord order) (power : ℕ) :
    (∑' cell : ℤ, cellFrequency cell ^ power *
      ‖closedDerivative (phaseWeightedJet parameters cell (field.val cell)) order word‖) ≤
      m15EvaluationConstant * originalGradeNorm (order + power + 3) field := by
  rw [← weighted_ordinaryGrade_norm parameters field]
  exact m15_frequencyWeighted_sup_tsum_le (weightedCoefficientCoreEquiv parameters field) word power

/-- Full real derivative of the accepted smooth extension, restricted to the
closed disk. All boundary values are the prescribed original jet. -/
def jetOperatorDerivative {dimension : ℕ} (order : ℕ) (field : ClosedJet dimension) :
    C(ClosedDisk, SpatialPlane [×order]→L[ℝ] ComplexEuclidean dimension) where
  toFun point := iteratedFDeriv ℝ order (smoothClosedExtension field) point.val
  continuous_toFun :=
    ((smoothClosedExtension_smooth field).continuous_iteratedFDeriv
      (by exact_mod_cast le_top)).comp continuous_subtype_val

theorem jetOperatorDerivative_eq_closedPlane {dimension order : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk) :
    jetOperatorDerivative order field point = closedPlaneHigherDerivative field point.val := by
  apply continuousMultilinearMap_ext_spatialPlaneBasis
  intro word
  change cartesianDerivative order word (smoothClosedExtension field) point.val = _
  rw [smoothClosedExtension_derivative, closedPlaneHigherDerivative_basis]
  congr 1
  apply Subtype.ext
  exact (ambientClosedDisk_val_of_mem point.property).symm

theorem jetOperatorDerivative_point_bound {dimension order : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk) :
    ‖jetOperatorDerivative order field point‖ ≤
      ∑ word : CartesianWord order,
        ‖spatialPlaneWordCoefficient word‖ * ‖closedDerivative field order word point‖ := by
  rw [jetOperatorDerivative_eq_closedPlane, closedPlaneHigherDerivative]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro word _
  have samePoint : ambientClosedDisk point.val = point := by
    apply Subtype.ext
    exact ambientClosedDisk_val_of_mem point.property
  rw [samePoint]
  exact (ContinuousMultilinearMap.norm_smulRight _ _).le

theorem jetOperatorDerivative_sup_bound {dimension order : ℕ}
    (field : ClosedJet dimension) :
    ‖jetOperatorDerivative order field‖ ≤
      ∑ word : CartesianWord order,
        ‖spatialPlaneWordCoefficient word‖ * ‖closedDerivative field order word‖ := by
  apply (ContinuousMap.norm_le _ (Finset.sum_nonneg
    (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))).2
  intro point
  apply (jetOperatorDerivative_point_bound field point).trans
  exact Finset.sum_le_sum (fun word _ => mul_le_mul_of_nonneg_left
    (ContinuousMap.norm_coe_le_norm _ point) (norm_nonneg _))

def wordOperatorFactor (order : ℕ) : ℝ :=
  ∑ word : CartesianWord order, ‖spatialPlaneWordCoefficient word‖

theorem wordOperatorFactor_nonnegative (order : ℕ) : 0 ≤ wordOperatorFactor order :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem weighted_operator_sup_summable {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (order power : ℕ) :
    Summable (fun cell : ℤ => cellFrequency cell ^ power *
      ‖jetOperatorDerivative order (phaseWeightedJet parameters cell (field.val cell))‖) := by
  let term (word : CartesianWord order) (cell : ℤ) : ℝ :=
    ‖spatialPlaneWordCoefficient word‖ * (cellFrequency cell ^ power *
      ‖closedDerivative (phaseWeightedJet parameters cell (field.val cell)) order word‖)
  have wordSummable (word : CartesianWord order) : Summable (term word) :=
    (weighted_word_sup_summable parameters field word power).mul_left
      ‖spatialPlaneWordCoefficient word‖
  have sumSummable : Summable (fun cell => ∑ word, term word cell) :=
    (hasSum_sum (fun word (_ : word ∈ (Finset.univ : Finset (CartesianWord order))) =>
      (wordSummable word).hasSum)).summable
  have dominated (cell : ℤ) : cellFrequency cell ^ power *
      ‖jetOperatorDerivative order (phaseWeightedJet parameters cell (field.val cell))‖ ≤
      ∑ word, term word cell := by
    calc
      _ ≤ cellFrequency cell ^ power * ∑ word : CartesianWord order,
          ‖spatialPlaneWordCoefficient word‖ *
            ‖closedDerivative (phaseWeightedJet parameters cell (field.val cell)) order word‖ :=
        mul_le_mul_of_nonneg_left
          (jetOperatorDerivative_sup_bound (order := order) (phaseWeightedJet parameters cell (field.val cell)))
          (pow_nonneg (cellFrequency_pos cell).le power)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro word _
        dsimp only [term]
        ring
  exact Summable.of_nonneg_of_le
    (fun cell => mul_nonneg (pow_nonneg (cellFrequency_pos cell).le power)
      (norm_nonneg (jetOperatorDerivative order (phaseWeightedJet parameters cell (field.val cell)))))
    dominated sumSummable

theorem weighted_operator_sup_tsum_bound {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (order power : ℕ) :
    (∑' cell : ℤ, cellFrequency cell ^ power *
      ‖jetOperatorDerivative order (phaseWeightedJet parameters cell (field.val cell))‖) ≤
      (wordOperatorFactor order * m15EvaluationConstant) *
        originalGradeNorm (order + power + 3) field := by
  have wordSummable (word : CartesianWord order) :=
    (weighted_word_sup_summable parameters field word power).mul_left
      ‖spatialPlaneWordCoefficient word‖
  calc
    _ ≤ ∑' cell : ℤ, ∑ word : CartesianWord order,
        ‖spatialPlaneWordCoefficient word‖ *
          (cellFrequency cell ^ power *
            ‖closedDerivative (phaseWeightedJet parameters cell (field.val cell)) order word‖) := by
      apply (weighted_operator_sup_summable parameters field order power).tsum_le_tsum _
        (hasSum_sum (fun word _ => (wordSummable word).hasSum)).summable
      intro cell
      calc
        _ ≤ cellFrequency cell ^ power * ∑ word : CartesianWord order,
            ‖spatialPlaneWordCoefficient word‖ *
              ‖closedDerivative (phaseWeightedJet parameters cell (field.val cell)) order word‖ :=
          mul_le_mul_of_nonneg_left (jetOperatorDerivative_sup_bound _)
            (pow_nonneg (cellFrequency_pos _).le _)
        _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    _ = ∑ word : CartesianWord order, ‖spatialPlaneWordCoefficient word‖ *
        ∑' cell : ℤ, cellFrequency cell ^ power *
          ‖closedDerivative (phaseWeightedJet parameters cell (field.val cell)) order word‖ := by
      rw [Summable.tsum_finsetSum (fun word _ => wordSummable word)]
      simp only [tsum_mul_left]
    _ ≤ ∑ word : CartesianWord order, ‖spatialPlaneWordCoefficient word‖ *
        (m15EvaluationConstant * originalGradeNorm (order + power + 3) field) :=
      Finset.sum_le_sum (fun word _ => mul_le_mul_of_nonneg_left
        (weighted_word_sup_tsum_bound parameters field word power) (norm_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; exact (mul_assoc _ _ _).symm

end Grad.NonlinearProduct
