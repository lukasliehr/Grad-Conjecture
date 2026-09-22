import OriginalCoefficientCore
import NGP01OperatorBound

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open Set MeasureTheory
open scoped BigOperators Topology

namespace Grad.CartesianState

open Grad.ClosedJets Grad.DiskExtension.Operator

local instance originalEvaluationCellPeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩

theorem originalField_coordinateDerivative_bound {dimension order j : ℕ}
    (parameters : PhaseParameters) (field : GradeCore parameters dimension (j + 3))
    (word : CartesianWord order) (cellOrder : ℕ) (orderLe : order + cellOrder ≤ j) :
    ‖ordinaryDerivativeExtension (originalCoefficientCore parameters field.toCore)
        word cellOrder‖ ≤ originalDerivativeSumConstant parameters order * ‖field‖ := by
  let coefficients := originalCoefficientCore parameters field.toCore
  let term : ℤ → C(DiskCellDomain, ComplexEuclidean dimension) := fun cell =>
    ordinaryDerivativeDiskCellTerm word cellOrder cell (coefficients.1 cell)
  have derivativeMajorant := physicalDerivative_series_summable coefficients word cellOrder
  have termNormSummable : Summable (fun cell : ℤ => ‖term cell‖) :=
    Summable.of_nonneg_of_le (fun cell => norm_nonneg (term cell))
      (fun cell => ordinaryDerivativeDiskCellTerm_norm_le word cellOrder cell
        (coefficients.1 cell)) derivativeMajorant
  have frequencyMajorant :=
    originalClosedDerivative_frequency_summable parameters field.toCore word cellOrder
  change ‖∑' cell : ℤ, term cell‖ ≤ _
  calc
    _ ≤ ∑' cell : ℤ, ‖term cell‖ := norm_tsum_le_tsum_norm termNormSummable
    _ ≤ ∑' cell : ℤ, cellFrequency cell ^ cellOrder *
        ‖closedDerivative (field.toCore.1 cell) order word‖ := by
      apply termNormSummable.tsum_le_tsum _ frequencyMajorant
      intro cell
      exact (ordinaryDerivativeDiskCellTerm_norm_le word cellOrder cell
        (coefficients.1 cell)).trans
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (abs_nonneg _) (cell_abs_le_frequency cell) cellOrder)
          (norm_nonneg _))
    _ ≤ _ := originalClosedDerivative_frequency_tsum_bound parameters field word cellOrder orderLe

def originalCoordinateConstant (parameters : PhaseParameters) (j : ℕ) : ℝ :=
  ∑ order : Fin (j + 1), originalDerivativeSumConstant parameters order.val

theorem originalCoordinateConstant_nonnegative (parameters : PhaseParameters) (j : ℕ) :
    0 ≤ originalCoordinateConstant parameters j :=
  Finset.sum_nonneg fun order _ => originalDerivativeSumConstant_nonnegative parameters order.val

theorem originalDerivativeSumConstant_le {order j : ℕ}
    (parameters : PhaseParameters) (orderLe : order ≤ j) :
    originalDerivativeSumConstant parameters order ≤ originalCoordinateConstant parameters j := by
  exact Finset.single_le_sum
    (fun index _ => originalDerivativeSumConstant_nonnegative parameters index.val)
    (Finset.mem_univ (⟨order, by omega⟩ : Fin (j + 1)))

theorem originalField_mixedCoordinateDerivative_bound {dimension order j : ℕ}
    (parameters : PhaseParameters) (field : GradeCore parameters dimension (j + 3))
    (word : MixedCartesianWord order) (orderLe : order ≤ j) :
    ‖closedMixedDerivative (originalPhysicalClosedJet parameters field.toCore) order word‖ ≤
      originalCoordinateConstant parameters j * ‖field‖ := by
  let coefficients := originalCoefficientCore parameters field.toCore
  let index := evaluationDerivativeIndexOfList (List.ofFn word)
  have totalIdentity : index.planarOrder + index.cellOrder = order := by
    change
      (evaluationDerivativeIndexOfList (List.ofFn word)
          evaluationDerivativeIndexZero).planarOrder +
        (evaluationDerivativeIndexOfList (List.ofFn word)
          evaluationDerivativeIndexZero).cellOrder = order
    rw [evaluationDerivativeIndexOfList_total]
    simp [evaluationDerivativeIndexZero]
  have totalLe : index.planarOrder + index.cellOrder ≤ j := totalIdentity.trans_le orderLe
  change ‖closedMixedDerivative (ordinaryReconstructedClosedJet coefficients) order word‖ ≤ _
  rw [← evaluationMixedDerivativeExtension_eq_closed coefficients word]
  change ‖ordinaryDerivativeExtension coefficients index.planarWord index.cellOrder‖ ≤ _
  exact (originalField_coordinateDerivative_bound parameters field
    index.planarWord index.cellOrder totalLe).trans
      (mul_le_mul_of_nonneg_right
        (originalDerivativeSumConstant_le parameters (by omega : index.planarOrder ≤ j))
        (norm_nonneg field))

def originalOperatorFactor (j : ℕ) : ℝ :=
  ∑ order : Fin (j + 1), ∑ word : MixedCartesianWord order.val,
    ‖spatialCellWordCoefficient word‖

theorem originalOperatorFactor_nonnegative (j : ℕ) : 0 ≤ originalOperatorFactor j :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

def originalPhysicalEvaluationConstant (parameters : PhaseParameters) (j : ℕ) : ℝ :=
  originalOperatorFactor j * originalCoordinateConstant parameters j

theorem originalPhysicalEvaluationConstant_nonnegative (parameters : PhaseParameters) (j : ℕ) :
    0 ≤ originalPhysicalEvaluationConstant parameters j :=
  mul_nonneg (originalOperatorFactor_nonnegative j)
    (originalCoordinateConstant_nonnegative parameters j)

theorem originalPhysicalOperatorDerivative_bound {dimension order j : ℕ}
    (parameters : PhaseParameters) (field : GradeCore parameters dimension (j + 3))
    (orderLe : order ≤ j) :
    ‖closedPhysicalOperatorDerivative (originalPhysicalClosedJet parameters field.toCore) order‖ ≤
      originalPhysicalEvaluationConstant parameters j * ‖field‖ := by
  refine (closedPhysicalOperatorDerivative_norm_le_bound _ order).trans ?_
  unfold closedHigherDerivativeBound
  have factorLe : (∑ word : MixedCartesianWord order, ‖spatialCellWordCoefficient word‖) ≤
      originalOperatorFactor j := by
    exact Finset.single_le_sum
      (f := fun rank : Fin (j + 1) =>
        ∑ word : MixedCartesianWord rank.val, ‖spatialCellWordCoefficient word‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ (⟨order, by omega⟩ : Fin (j + 1)))
  calc
    _ ≤ ∑ word : MixedCartesianWord order, ‖spatialCellWordCoefficient word‖ *
        (originalCoordinateConstant parameters j * ‖field‖) := by
      apply Finset.sum_le_sum
      intro word _membership
      exact mul_le_mul_of_nonneg_left
        (originalField_mixedCoordinateDerivative_bound parameters field word orderLe)
        (norm_nonneg _)
    _ = (∑ word : MixedCartesianWord order, ‖spatialCellWordCoefficient word‖) *
        (originalCoordinateConstant parameters j * ‖field‖) := by rw [Finset.sum_mul]
    _ ≤ originalOperatorFactor j * (originalCoordinateConstant parameters j * ‖field‖) :=
      mul_le_mul_of_nonneg_right factorLe
        (mul_nonneg (originalCoordinateConstant_nonnegative parameters j) (norm_nonneg field))
    _ = originalPhysicalEvaluationConstant parameters j * ‖field‖ := by
      unfold originalPhysicalEvaluationConstant
      ring

/-- Exact original-field `A^(j+3)` to the literal maximum of Euclidean
multilinear operator norms through order `j`. -/
theorem originalField_closedPhysicalCNorm_bound {dimension j : ℕ}
    (parameters : PhaseParameters) (field : GradeCore parameters dimension (j + 3)) :
    closedPhysicalCNorm (originalPhysicalClosedJet parameters field.toCore) j ≤
      originalPhysicalEvaluationConstant parameters j * ‖field‖ := by
  unfold closedPhysicalCNorm
  rw [Finset.max'_le_iff]
  intro value membership
  rw [physicalDerivativeNorms, Finset.mem_image] at membership
  obtain ⟨order, _, rfl⟩ := membership
  exact originalPhysicalOperatorDerivative_bound parameters field
    (Nat.lt_succ_iff.mp order.isLt)

end Grad.CartesianState
