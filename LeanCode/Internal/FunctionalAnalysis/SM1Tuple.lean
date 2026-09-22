import SM1Field
import SM1Indices

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue FieldL2)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets.SpatialMultiplier

theorem difference_self {order : ℕ} (index : JetIndex order) :
    difference index index = zeroIndex order := by
  apply Subtype.ext
  change (index.val.1 - index.val.1, index.val.2 - index.val.2) = (0, 0)
  simp only [Nat.sub_self]

theorem binomial_self {order : ℕ} (index : JetIndex order) : binomial index index = 1 := by
  simp [binomial]

theorem coordinateMultiplier_apply (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol order domain)
    (exponent : JetIndex order → ℕ) (upper : JetIndex order) (tuple : JetTuple dimension order domain) :
    coordinateMultiplier dimension order domain openDomain symbol exponent upper tuple =
      ∑ lower ∈ below upper, (binomial upper lower : ℂ) •
        fieldMultiplier dimension domain openDomain (derivativeScalar symbol (difference upper lower))
          (Grad.CellWeights.inverseFieldCLM dimension domain (exponent lower - exponent upper)
            (tuple lower)) := by
  simp only [coordinateMultiplier, sum_apply, smul_apply, ContinuousLinearMap.comp_apply, coordinate_apply]

theorem tupleMultiplier_apply (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol order domain)
    (exponent : JetIndex order → ℕ) (tuple : JetTuple dimension order domain) (upper : JetIndex order) :
    tupleMultiplier dimension order domain openDomain symbol exponent tuple upper =
      coordinateMultiplier dimension order domain openDomain symbol exponent upper tuple := rfl

theorem unweightedCoordinate_apply (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol order domain)
    (exponent : JetIndex order → ℕ) (upper : JetIndex order)
    (jet : WJet dimension order domain exponent) :
    unweightedCoordinate dimension order domain openDomain symbol exponent upper jet =
      ∑ lower ∈ below upper, (binomial upper lower : ℂ) •
        fieldMultiplier dimension domain openDomain (derivativeScalar symbol (difference upper lower))
          (Realization.recoveredDerivative dimension order domain exponent lower jet) := by
  simp only [unweightedCoordinate, sum_apply, smul_apply, ContinuousLinearMap.comp_apply]

theorem matrixEntry_nonnegative {order : ℕ} {domain : Set Spatial} (symbol : Symbol order domain)
    (upper lower : JetIndex order) : 0 ≤ matrixEntry symbol upper lower := by
  classical
  unfold matrixEntry
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _) (symbol.bound _).property
  · exact le_rfl

theorem rowBound_nonnegative {order : ℕ} {domain : Set Spatial} (symbol : Symbol order domain)
    (upper : JetIndex order) : 0 ≤ rowBound symbol upper :=
  Finset.sum_nonneg (fun lower _ => matrixEntry_nonnegative symbol upper lower)

theorem rowBound_eq {order : ℕ} {domain : Set Spatial} (symbol : Symbol order domain)
    (upper : JetIndex order) :
    rowBound symbol upper =
      ∑ lower ∈ below upper, (binomial upper lower : ℝ) * symbol.bound (difference upper lower) := by
  classical
  simp only [rowBound, matrixEntry, below, Finset.sum_filter]

theorem coordinateMultiplier_norm_le (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (tuple : JetTuple dimension order domain) (upper : JetIndex order) :
    ‖coordinateMultiplier dimension order domain openDomain symbol exponent upper tuple‖ ≤
      rowBound symbol upper * ‖tuple‖ := by
  classical
  rw [coordinateMultiplier_apply, rowBound_eq, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro lower membership
  rw [norm_smul, Complex.norm_natCast, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  refine (fieldMultiplier_apply_norm_le dimension domain openDomain
    (derivativeScalar symbol (difference upper lower)) _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (symbol.bound _).property
  exact (Inclusions.inverse_norm_le dimension domain _ (tuple lower)).trans
    (PiLp.norm_apply_le tuple lower)

theorem tupleMultiplier_norm_sq (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (tuple : JetTuple dimension order domain) :
    ‖tupleMultiplier dimension order domain openDomain symbol exponent tuple‖ ^ 2 =
      ∑ upper, ‖coordinateMultiplier dimension order domain openDomain symbol exponent upper tuple‖ ^ 2 := by
  rw [tuple_norm_sq]
  rfl

theorem tupleMultiplier_apply_norm_le (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (tuple : JetTuple dimension order domain) :
    ‖tupleMultiplier dimension order domain openDomain symbol exponent tuple‖ ≤
      matrixBound symbol * ‖tuple‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [tupleMultiplier_norm_sq]
  calc
    _ ≤ ∑ upper : JetIndex order, (rowBound symbol upper * ‖tuple‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro upper membership
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (rowBound_nonnegative symbol upper) (norm_nonneg _))).mpr
        (coordinateMultiplier_norm_le dimension order domain openDomain symbol exponent tuple upper)
    _ = (matrixBound symbol * ‖tuple‖) ^ 2 := by
      simp only [mul_pow, matrixBound, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
        Finset.sum_mul]

theorem tupleMultiplier_norm_le (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol order domain) (exponent : JetIndex order → ℕ) :
    ‖tupleMultiplier dimension order domain openDomain symbol exponent‖ ≤ matrixBound symbol :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    (tupleMultiplier_apply_norm_le dimension order domain openDomain symbol exponent)

theorem tuple_consumer : TupleGoal := by
  intro dimension order domain openDomain symbol exponent
  exact ⟨fun tuple upper => (tupleMultiplier_apply dimension order domain openDomain symbol exponent tuple upper).trans
      (coordinateMultiplier_apply dimension order domain openDomain symbol exponent upper tuple),
    tupleMultiplier_norm_sq dimension order domain openDomain symbol exponent,
    matrixEntry_nonnegative symbol,
    coordinateMultiplier_norm_le dimension order domain openDomain symbol exponent,
    tupleMultiplier_norm_le dimension order domain openDomain symbol exponent⟩

theorem unweightedCoordinate_zero (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (jet : WJet dimension order domain exponent) :
    unweightedCoordinate dimension order domain openDomain symbol exponent (zeroIndex order) jet =
      fieldMultiplier dimension domain openDomain (derivativeScalar symbol (zeroIndex order))
        (base dimension order domain exponent jet) := by
  rw [unweightedCoordinate_apply, below_zero, Finset.sum_singleton, binomial_self,
    difference_self, Nat.cast_one, one_smul]
  rfl

theorem tupleMultiplier_base (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (tuple : JetTuple dimension order domain) :
    ambientBase dimension order domain exponent
        (tupleMultiplier dimension order domain openDomain symbol exponent tuple) =
      fieldMultiplier dimension domain openDomain (derivativeScalar symbol (zeroIndex order))
        (ambientBase dimension order domain exponent tuple) := by
  rw [ambientBase_apply, tupleMultiplier_apply, coordinateMultiplier_apply, below_zero,
    Finset.sum_singleton, binomial_self, difference_self, Nat.cast_one, one_smul,
    Nat.sub_self, Grad.CellWeights.inverseFieldCLM_zero, ContinuousLinearMap.id_apply]
  exact (congrArg (fun operator : FieldL2 dimension domain →L[ℂ] FieldL2 dimension domain =>
    operator (tuple (zeroIndex order))) (fieldMultiplier_inverse dimension domain openDomain
      (derivativeScalar symbol (zeroIndex order)) (exponent (zeroIndex order)))).symm

theorem tupleMultiplier_recovery (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (compatible : ExponentAntitone exponent) (upper : JetIndex order)
    (jet : WJet dimension order domain exponent) :
    Grad.CellWeights.inverseFieldCLM dimension domain (exponent upper)
        (tupleMultiplier dimension order domain openDomain symbol exponent jet.val upper) =
      unweightedCoordinate dimension order domain openDomain symbol exponent upper jet := by
  rw [tupleMultiplier_apply, coordinateMultiplier_apply, unweightedCoordinate_apply, map_sum]
  apply Finset.sum_congr rfl
  intro lower membership
  rw [map_smul]
  congr 1
  have commutation := congrArg
    (fun operator : FieldL2 dimension domain →L[ℂ] FieldL2 dimension domain =>
      operator (Grad.CellWeights.inverseFieldCLM dimension domain (exponent lower - exponent upper)
        (jet.val lower)))
    (fieldMultiplier_inverse dimension domain openDomain
      (derivativeScalar symbol (difference upper lower)) (exponent upper))
  simp only [ContinuousLinearMap.comp_apply] at commutation
  rw [← commutation]
  have composition := congrArg
    (fun operator : FieldL2 dimension domain →L[ℂ] FieldL2 dimension domain => operator (jet.val lower))
    (Grad.CellWeights.inverseFieldCLM_comp dimension domain (exponent upper)
      (exponent lower - exponent upper))
  have powers : exponent upper + (exponent lower - exponent upper) = exponent lower :=
    Nat.add_sub_of_le (compatible lower upper ((mem_below _ _).mp membership))
  simpa only [ContinuousLinearMap.comp_apply, powers, Realization.recoveredDerivative_apply] using congrArg
    (fieldMultiplier dimension domain openDomain (derivativeScalar symbol (difference upper lower))) composition

end Grad.WeightedJets.SpatialMultiplier
