import GC14InversePhase

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open Set MeasureTheory
open scoped BigOperators Topology

namespace Grad.CartesianState

open Grad.ClosedJets

/-- The phase multiplies the original derivative after differentiation. -/
def phaseOutsideClosedDerivative {dimension : ℕ} (parameters : PhaseParameters)
    (cell : ℤ) (field : ClosedJet dimension) (order : ℕ) (word : CartesianWord order) :
    C(ClosedDisk, ComplexEuclidean dimension) where
  toFun point := cartesianWeight parameters cell point.val •
    closedDerivative field order word point
  continuous_toFun :=
    ((cartesianWeight_contDiff parameters cell).continuous.comp continuous_subtype_val).smul
      (closedDerivative field order word).continuous

theorem phaseOutsideClosedDerivative_norm_bound {dimension : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (order : ℕ) (word : CartesianWord order) :
    ‖phaseOutsideClosedDerivative parameters cell field order word‖ ≤
      ∑ selected : Finset (Fin order),
        inversePhaseDerivativeConstant parameters selected.card *
          cellFrequency cell ^ selected.card *
          ‖closedDerivative (phaseWeightedJet parameters cell field) selectedᶜ.card
            (Grad.RepresentedKernel.SpatialProduct.subword word selectedᶜ)‖ := by
  apply (ContinuousMap.norm_le _ (Finset.sum_nonneg fun selected _ =>
    mul_nonneg (mul_nonneg (inversePhaseDerivativeConstant_nonnegative parameters _)
      (pow_nonneg (cellFrequency_pos cell).le _)) (norm_nonneg _))).2
  intro point
  change ‖cartesianWeight parameters cell point.val •
    closedDerivative field order word point‖ ≤ _
  rw [norm_smul, Real.norm_of_nonneg (cartesianWeight_pos parameters cell point.val).le]
  exact originalWeight_closedDerivative_point_bound parameters cell field order word point

theorem phaseOutsideClosedDerivative_frequency_bound {dimension : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (order : ℕ) (word : CartesianWord order) (cellOrder : ℕ) :
    cellFrequency cell ^ cellOrder *
        ‖phaseOutsideClosedDerivative parameters cell field order word‖ ≤
      ∑ selected : Finset (Fin order),
        inversePhaseDerivativeConstant parameters selected.card *
          (cellFrequency cell ^ (cellOrder + selected.card) *
            ‖closedDerivative (phaseWeightedJet parameters cell field) selectedᶜ.card
              (Grad.RepresentedKernel.SpatialProduct.subword word selectedᶜ)‖) := by
  calc
    _ ≤ cellFrequency cell ^ cellOrder *
      ∑ selected : Finset (Fin order),
        inversePhaseDerivativeConstant parameters selected.card *
          cellFrequency cell ^ selected.card *
          ‖closedDerivative (phaseWeightedJet parameters cell field) selectedᶜ.card
            (Grad.RepresentedKernel.SpatialProduct.subword word selectedᶜ)‖ :=
      mul_le_mul_of_nonneg_left
        (phaseOutsideClosedDerivative_norm_bound parameters cell field order word)
        (pow_nonneg (cellFrequency_pos cell).le _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro selected _membership
      rw [pow_add]
      ring

theorem phaseOutsideClosedDerivative_frequency_summable {dimension order : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (word : CartesianWord order) (cellOrder : ℕ) :
    Summable (fun cell : ℤ => cellFrequency cell ^ cellOrder *
      ‖phaseOutsideClosedDerivative parameters cell (field.1 cell) order word‖) := by
  let coefficients := weightedCoefficientCoreEquiv parameters field
  have each (selected : Finset (Fin order)) : Summable (fun cell : ℤ =>
      inversePhaseDerivativeConstant parameters selected.card *
        (cellFrequency cell ^ (cellOrder + selected.card) *
          ‖closedDerivative (phaseWeightedJet parameters cell (field.1 cell)) selectedᶜ.card
            (Grad.RepresentedKernel.SpatialProduct.subword word selectedᶜ)‖)) :=
    (m15_frequencyWeighted_sup_summable coefficients
      (Grad.RepresentedKernel.SpatialProduct.subword word selectedᶜ)
      (cellOrder + selected.card)).mul_left
        (inversePhaseDerivativeConstant parameters selected.card)
  exact Summable.of_nonneg_of_le
    (fun cell => mul_nonneg (pow_nonneg (cellFrequency_pos cell).le _) (norm_nonneg _))
    (fun cell => phaseOutsideClosedDerivative_frequency_bound parameters cell
      (field.1 cell) order word cellOrder)
    (hasSum_sum (fun selected _ => (each selected).hasSum)).summable

def originalDerivativeSumConstant (parameters : PhaseParameters) (order : ℕ) : ℝ :=
  (∑ selected : Finset (Fin order),
    inversePhaseDerivativeConstant parameters selected.card) * m15EvaluationConstant

theorem originalDerivativeSumConstant_nonnegative (parameters : PhaseParameters)
    (order : ℕ) : 0 ≤ originalDerivativeSumConstant parameters order := by
  exact mul_nonneg (Finset.sum_nonneg fun selected _ =>
    inversePhaseDerivativeConstant_nonnegative parameters selected.card)
      m15EvaluationConstant_nonneg

theorem ordinaryGradeCoordinates_weighted_le {dimension lower upper : ℕ}
    (parameters : PhaseParameters) (field : GradeCore parameters dimension upper)
    (gradeLe : lower ≤ upper) :
    ‖ordinaryGradeCoordinates lower (weightedCoefficientCoreEquiv parameters field.toCore)‖ ≤
      ‖field‖ := by
  have identity :
      ‖ordinaryGradeCoordinates lower (weightedCoefficientCoreEquiv parameters field.toCore)‖ =
        ‖GradeCore.ofCoreLinear (grade := lower) field.toCore‖ := by
    rw [ordinaryGradeCoordinates_weighted_norm,
      gradeCore_norm_eq_cartesianGradeSeminorm,
      cartesianGradeSeminorm_apply, gradeCoreCoordinates_apply]
    rfl
  rw [identity]
  simpa only [GradeCore.ofCore_toCore] using
    cartesianGrade_norm_mono parameters gradeLe field.toCore

/-- The supremum precedes the sum over cells, and only three grades are spent. -/
theorem phaseOutsideClosedDerivative_frequency_tsum_bound {dimension order j : ℕ}
    (parameters : PhaseParameters) (field : GradeCore parameters dimension (j + 3))
    (word : CartesianWord order) (cellOrder : ℕ) (orderLe : order + cellOrder ≤ j) :
    ∑' cell : ℤ, cellFrequency cell ^ cellOrder *
        ‖phaseOutsideClosedDerivative parameters cell (field.toCore.1 cell) order word‖ ≤
      originalDerivativeSumConstant parameters order * ‖field‖ := by
  let coefficients := weightedCoefficientCoreEquiv parameters field.toCore
  let term (selected : Finset (Fin order)) (cell : ℤ) :=
    inversePhaseDerivativeConstant parameters selected.card *
      (cellFrequency cell ^ (cellOrder + selected.card) *
        ‖closedDerivative (coefficients.1 cell) selectedᶜ.card
          (Grad.RepresentedKernel.SpatialProduct.subword word selectedᶜ)‖)
  have each (selected : Finset (Fin order)) : Summable (term selected) :=
    (m15_frequencyWeighted_sup_summable coefficients
      (Grad.RepresentedKernel.SpatialProduct.subword word selectedᶜ)
      (cellOrder + selected.card)).mul_left
        (inversePhaseDerivativeConstant parameters selected.card)
  calc
    _ ≤ ∑' cell : ℤ, ∑ selected : Finset (Fin order), term selected cell :=
      (phaseOutsideClosedDerivative_frequency_summable parameters field.toCore word cellOrder).tsum_le_tsum
          (fun cell => phaseOutsideClosedDerivative_frequency_bound parameters cell
            (field.toCore.1 cell) order word cellOrder)
          (hasSum_sum (fun selected _ => (each selected).hasSum)).summable
    _ = ∑ selected : Finset (Fin order), ∑' cell : ℤ, term selected cell := by
      rw [Summable.tsum_finsetSum (fun selected _ => each selected)]
    _ ≤ ∑ selected : Finset (Fin order),
        inversePhaseDerivativeConstant parameters selected.card *
          (m15EvaluationConstant * ‖field‖) := by
      apply Finset.sum_le_sum
      intro selected _membership
      unfold term
      rw [tsum_mul_left]
      apply mul_le_mul_of_nonneg_left _
        (inversePhaseDerivativeConstant_nonnegative parameters selected.card)
      refine (m15_frequencyWeighted_sup_tsum_le coefficients
        (Grad.RepresentedKernel.SpatialProduct.subword word selectedᶜ)
        (cellOrder + selected.card)).trans ?_
      apply mul_le_mul_of_nonneg_left _ m15EvaluationConstant_nonneg
      apply ordinaryGradeCoordinates_weighted_le parameters field
      have cardinality : selected.card + selectedᶜ.card = order := by
        simp
      unfold m15Grade
      omega
    _ = originalDerivativeSumConstant parameters order * ‖field‖ := by
      unfold originalDerivativeSumConstant
      rw [← Finset.sum_mul]
      ring

end Grad.CartesianState
