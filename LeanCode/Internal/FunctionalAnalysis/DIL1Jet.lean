import DIL1Weak

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (CellValues PhysicalValue FieldL2)
open Grad.WeightedJets
open scoped BigOperators ContDiff

namespace Grad.SpatialDilation

theorem tupleValue_coordinate_norm (dimension order : ℕ) (radius : ℝ) (scale : Scale)
    (tuple : JetTuple dimension order (disk radius)) (index : JetIndex order) :
    ‖tupleValue dimension order radius scale tuple index‖ =
      scale.val ^ degree index * (scale.val⁻¹ * ‖tuple index‖) := by
  change ‖(scale.val ^ degree index : ℂ) •
    rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale (tuple index)‖ = _
  calc
    _ = ‖(scale.val ^ degree index : ℂ)‖ *
        ‖rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale (tuple index)‖ := norm_smul _ _
    _ = scale.val ^ degree index *
        ‖rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale (tuple index)‖ := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos scale.property.1]
    _ = _ := congrArg (fun value : ℝ => scale.val ^ degree index * value)
      (rawValue_norm dimension (disk radius) Metric.isOpen_ball.measurableSet scale (tuple index))

theorem tupleValue_coordinate_bound (dimension order : ℕ) (radius : ℝ) (scale : Scale)
    (tuple : JetTuple dimension order (disk radius)) (index : JetIndex order) :
    ‖tupleValue dimension order radius scale tuple index‖ ≤ scale.val⁻¹ * ‖tuple index‖ := by
  rw [tupleValue_coordinate_norm]
  exact mul_le_of_le_one_left (mul_nonneg (inv_nonneg.mpr scale.property.1.le) (norm_nonneg _))
    (pow_le_one₀ scale.property.1.le scale.property.2)

theorem tupleValue_norm_le (dimension order : ℕ) (radius : ℝ) (scale : Scale)
    (tuple : JetTuple dimension order (disk radius)) :
    ‖tupleValue dimension order radius scale tuple‖ ≤ scale.val⁻¹ * ‖tuple‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr scale.property.1.le) (norm_nonneg _))).mp
  calc
    _ = ∑ index : JetIndex order, ‖tupleValue dimension order radius scale tuple index‖ ^ 2 :=
      tuple_norm_sq dimension order (expandedDisk radius scale) _
    _ ≤ ∑ index : JetIndex order, (scale.val⁻¹ * ‖tuple index‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro index _membership
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr scale.property.1.le) (norm_nonneg _))).mpr
        (tupleValue_coordinate_bound dimension order radius scale tuple index)
    _ = _ := by
      rw [mul_pow, tuple_norm_sq, Finset.mul_sum]
      simp only [mul_pow]

theorem degree_factor_square (scale : Scale) (rank : ℕ) :
    (scale.val ^ rank) ^ 2 * (scale.val⁻¹) ^ 2 = scale.val ^ (2 * (rank : ℤ) - 2) := by
  rw [zpow_sub₀ scale.property.1.ne']
  have powers : scale.val ^ (2 * (rank : ℤ)) = (scale.val ^ rank) ^ 2 := by
    rw [mul_comm (2 : ℤ), zpow_mul]
    simp only [zpow_natCast]
    rfl
  rw [powers]
  simp only [div_eq_mul_inv, inv_pow]
  rfl

theorem tupleValue_norm_sq (dimension order : ℕ) (radius : ℝ) (scale : Scale)
    (tuple : JetTuple dimension order (disk radius)) :
    ‖tupleValue dimension order radius scale tuple‖ ^ 2 =
      ∑ index : JetIndex order, scale.val ^ (2 * (degree index : ℤ) - 2) * ‖tuple index‖ ^ 2 := by
  rw [tuple_norm_sq]
  apply Finset.sum_congr rfl
  intro index _membership
  rw [tupleValue_coordinate_norm, mul_pow, mul_pow, ← mul_assoc, degree_factor_square]

theorem tuple_goal : TupleGoal := by
  intro dimension order radius scale tuple
  refine ⟨tupleValue_norm_sq dimension order radius scale tuple,
    tupleValue_norm_le dimension order radius scale tuple, ?_⟩
  intro exponent membership
  exact tupleValue_mem_graph dimension order radius scale exponent ⟨tuple, membership⟩

def jetDilationLinear (dimension order : ℕ) (radius : ℝ) (scale : Scale) (exponent : JetIndex order → ℕ) :
    WJet dimension order (disk radius) exponent →ₗ[ℂ] WJet dimension order (expandedDisk radius scale) exponent where
  toFun jet := ⟨tupleValue dimension order radius scale jet.val,
    tupleValue_mem_graph dimension order radius scale exponent jet⟩
  map_add' first second := by
    apply jet_eq
    intro index
    change (scale.val ^ degree index : ℂ) • rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale
        (first.val index + second.val index) = _
    erw [rawValue_add, smul_add]
    rfl
  map_smul' scalar jet := by
    apply jet_eq
    intro index
    change (scale.val ^ degree index : ℂ) • rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale
        (scalar • jet.val index) = scalar • _
    erw [rawValue_smul, smul_comm]
    rfl

def jetDilation (dimension order : ℕ) (radius : ℝ) (scale : Scale) (exponent : JetIndex order → ℕ) :
    WJet dimension order (disk radius) exponent →L[ℂ] WJet dimension order (expandedDisk radius scale) exponent :=
  (jetDilationLinear dimension order radius scale exponent).mkContinuous scale.val⁻¹
    (fun jet => tupleValue_norm_le dimension order radius scale jet.val)

theorem jetDilation_tuple (dimension order : ℕ) (radius : ℝ) (scale : Scale)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order (disk radius) exponent) :
    (jetDilation dimension order radius scale exponent jet).val = tupleValue dimension order radius scale jet.val := rfl

theorem jetDilation_norm_le (dimension order : ℕ) (radius : ℝ) (scale : Scale)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order (disk radius) exponent) :
    ‖jetDilation dimension order radius scale exponent jet‖ ≤ scale.val⁻¹ * ‖jet‖ :=
  tupleValue_norm_le dimension order radius scale jet.val

theorem jetDilation_opNorm_le (dimension order : ℕ) (radius : ℝ) (scale : Scale)
    (exponent : JetIndex order → ℕ) : ‖jetDilation dimension order radius scale exponent‖ ≤ scale.val⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr scale.property.1.le)
  exact jetDilation_norm_le dimension order radius scale exponent

theorem jetDilation_base (dimension order : ℕ) (radius : ℝ) (scale : Scale)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order (disk radius) exponent) :
    base dimension order (expandedDisk radius scale) exponent (jetDilation dimension order radius scale exponent jet) =
      rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale
        (base dimension order (disk radius) exponent jet) :=
  tupleValue_base dimension order radius scale exponent jet.val

theorem jetDilation_recovery (dimension order : ℕ) (radius : ℝ) (scale : Scale)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order (disk radius) exponent) (index : JetIndex order) :
    Realization.recoveredDerivative dimension order (expandedDisk radius scale) exponent index
        (jetDilation dimension order radius scale exponent jet) =
      (scale.val ^ degree index : ℂ) • rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale
        (Realization.recoveredDerivative dimension order (disk radius) exponent index jet) :=
  tupleValue_recovery dimension order radius scale exponent jet.val index

theorem jetDilation_coordinates (dimension order : ℕ) (radius : ℝ) (scale : Scale)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order (disk radius) exponent) :
    ∀ᵐ point ∂volume.restrict (expandedDisk radius scale), ∀ (index : JetIndex order) (cell : ℤ),
      (jetDilation dimension order radius scale exponent jet).val index point cell =
        (scale.val ^ degree index : ℂ) • jet.val index (scale.val • point) cell := by
  have each : ∀ index : JetIndex order,
      ∀ᵐ point ∂volume.restrict (expandedDisk radius scale),
        (jetDilation dimension order radius scale exponent jet).val index point =
          (scale.val ^ degree index : ℂ) • jet.val index (scale.val • point) := by
    intro index
    filter_upwards [rawValue_ae dimension (disk radius) Metric.isOpen_ball.measurableSet scale (jet.val index),
      Lp.coeFn_smul (scale.val ^ degree index : ℂ)
        (rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale (jet.val index))]
      with point sourceAt targetAt
    change ((scale.val ^ degree index : ℂ) •
      rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale (jet.val index)) point = _
    rw [targetAt, Pi.smul_apply, sourceAt]
  filter_upwards [ae_all_iff.mpr each] with point represented
  intro index cell
  exact congrArg (fun values : CellValues dimension => values cell) (represented index)

theorem jetDilation_laws (dimension order : ℕ) (radius : ℝ) (scale : Scale) (exponent : JetIndex order → ℕ) :
    JetLaws dimension order radius scale exponent (jetDilation dimension order radius scale exponent) := by
  refine ⟨jetDilation_opNorm_le dimension order radius scale exponent, ?_⟩
  intro jet
  exact ⟨rfl, tupleValue_norm_sq dimension order radius scale jet.val,
    jetDilation_norm_le dimension order radius scale exponent jet,
    jetDilation_base dimension order radius scale exponent jet,
    jetDilation_recovery dimension order radius scale exponent jet,
    jetDilation_coordinates dimension order radius scale exponent jet,
    fun index cell vector test => Realization.recoveredDerivative_integral dimension order
      (expandedDisk radius scale) exponent index (jetDilation dimension order radius scale exponent jet) cell vector test⟩

end Grad.SpatialDilation
