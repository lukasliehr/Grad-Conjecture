import ClosedJetOrthogonalL2

noncomputable section

open Set Grad.ClosedJets Grad.CartesianState
open Grad.RepresentedKernel.SpatialProduct Grad.GaugeCoefficients.Radial
open Grad.WeakTesting.Commutation
open scoped BigOperators ContDiff Topology

namespace Grad.Constraints

theorem closedDerivative_eq_multi {dimension order : ℕ} (field : ClosedJet dimension)
    (word : CartesianWord order) :
    closedDerivative field order word = closedMultiDerivative field (orthogonalTargetIndex word) := by
  apply continuousMap_eq_of_openDisk
  intro point inside
  rw [closedDerivative_spec field order word point inside]
  generalize zeroEquality : directionCount word 0 = zeros
  generalize oneEquality : directionCount word 1 = ones
  have cardinality : zeros + ones = order := by
    rw [← zeroEquality, ← oneEquality]
    exact count_total order word
  subst order
  unfold orthogonalTargetIndex
  rw [zeroEquality, oneEquality]
  change cartesianDerivative (zeros + ones) word (closedDiskLift field.value) point.val =
    closedDerivative field (zeros + ones) (cartesianMultiIndexWord (zeros, ones)) point
  rw [closedDerivative_spec field (zeros + ones) (cartesianMultiIndexWord (zeros, ones))
    point inside]
  exact wordDerivative_canonical openUnitDisk_isOpen zeros ones word zeroEquality oneEquality
    field.smoothInterior inside

def wordGradeIndex {grade order : ℕ} (orderBound : order ≤ grade)
    (word : CartesianWord order) : GradeMultiIndex grade :=
  (gradeMultiIndexEquiv grade).symm ⟨orthogonalTargetIndex word, by
    change directionCount word 0 + directionCount word 1 ≤ grade
    rw [count_total]
    exact orderBound⟩

theorem wordGradeIndex_cartesian {grade order : ℕ} (orderBound : order ≤ grade)
    (word : CartesianWord order) :
    (wordGradeIndex orderBound word).toCartesian = orthogonalTargetIndex word := rfl

theorem wordGradeIndex_order {grade order : ℕ} (orderBound : order ≤ grade)
    (word : CartesianWord order) :
    cartesianOrder (wordGradeIndex orderBound word).toCartesian = order :=
  count_total order word

theorem weighted_word_norm_le_row {dimension grade order : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (orderBound : order ≤ grade) (word : CartesianWord order) :
    cellFrequency cell ^ (grade - order) *
      ‖closedContinuousToDiskL2 (closedDerivative (phaseWeightedJet parameters cell field)
        order word)‖ ≤ ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
  have bound := PiLp.norm_apply_le
    (cellGradeRowLinear (grade := grade) parameters cell field) (wordGradeIndex orderBound word)
  rw [cellGradeRowLinear_apply, norm_smul, Complex.norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (cellFrequency_pos cell), wordGradeIndex_order,
    wordGradeIndex_cartesian] at bound
  rw [closedDerivative_eq_multi]
  exact bound

theorem orthogonalDerivative_eq_sum {dimension order : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ClosedJet dimension)
    (word : CartesianWord order) :
    orthogonalDerivative orthogonal field order word =
      ∑ target : CartesianWord order, (chainFactor order orthogonal word target : ℂ) •
        (closedDerivative field order target).comp (orthogonalClosedMap orthogonal) := by
  apply ContinuousMap.ext
  intro point
  rw [continuousMap_sum_apply]
  change (∑ target : CartesianWord order, chainFactor order orthogonal word target •
    closedDerivative field order target (orthogonalClosedPoint orthogonal point)) = _
  apply Finset.sum_congr rfl
  intro target _
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _

theorem orthogonal_derivative_L2_norm_le {dimension order : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ClosedJet dimension)
    (word : CartesianWord order) :
    ‖closedContinuousToDiskL2 (closedDerivative (orthogonalJet orthogonal field) order word)‖ ≤
      ∑ target : CartesianWord order, ‖closedContinuousToDiskL2
        (closedDerivative field order target)‖ := by
  rw [orthogonalJet_derivative, orthogonalDerivative_eq_sum]
  change ‖closedValueL2Linear dimension (∑ target : CartesianWord order,
    (chainFactor order orthogonal word target : ℂ) •
      (closedDerivative field order target).comp (orthogonalClosedMap orthogonal))‖ ≤ _
  rw [map_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro target _
  rw [map_smul]
  change ‖(chainFactor order orthogonal word target : ℂ) •
    closedContinuousToDiskL2 ((closedDerivative field order target).comp
      (orthogonalClosedMap orthogonal))‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, closedValueL2_orthogonal_norm]
  exact mul_le_of_le_one_left (norm_nonneg _) (chainFactor_abs_le_one _ orthogonal _ _)

theorem weighted_orthogonal_word_norm_le {dimension grade order : ℕ}
    (parameters : PhaseParameters) (cell : ℤ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ClosedJet dimension)
    (orderBound : order ≤ grade) (word : CartesianWord order) :
    cellFrequency cell ^ (grade - order) *
      ‖closedContinuousToDiskL2 (closedDerivative
        (phaseWeightedJet parameters cell (orthogonalJet orthogonal field)) order word)‖ ≤
      (2 : ℝ) ^ grade * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
  rw [← orthogonalJet_phaseWeighted]
  calc
    _ ≤ cellFrequency cell ^ (grade - order) *
        ∑ target : CartesianWord order,
          ‖closedContinuousToDiskL2 (closedDerivative
            (phaseWeightedJet parameters cell field) order target)‖ :=
      mul_le_mul_of_nonneg_left (orthogonal_derivative_L2_norm_le orthogonal _ word)
        (pow_nonneg (cellFrequency_pos cell).le _)
    _ = ∑ target : CartesianWord order, cellFrequency cell ^ (grade - order) *
        ‖closedContinuousToDiskL2 (closedDerivative
          (phaseWeightedJet parameters cell field) order target)‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ _target : CartesianWord order,
        ‖cellGradeRowLinear (grade := grade) parameters cell field‖ :=
      Finset.sum_le_sum (fun target _ => weighted_word_norm_le_row parameters cell field orderBound target)
    _ = (2 : ℝ) ^ order * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) orderBound) (norm_nonneg _)

end Grad.Constraints
