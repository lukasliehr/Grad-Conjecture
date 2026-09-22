import ACB4NativeResolventGradient

noncomputable section
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterBounds
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.ActualCenterVolterra Grad.CircularHighWeak
open Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger (apRow_norm_bound_of_coordinates)

theorem partial_coordinate_value_norm {dimension : ℕ} (direction coordinate : Fin 2) (field : ClosedJet dimension) :
    ‖(partialJet direction (coordinateJet coordinate field)).value‖ ≤
      ‖field.value‖ + ‖(partialJet direction field).value‖ := by
  have coefficient : ‖((spatialBasis direction coordinate : ℝ) : ℂ)‖ ≤ 1 := by
    simp [spatialBasis, PiLp.single_apply]
    split_ifs <;> norm_num
  rw [centerPartial_coordinate, closedJet_value_add, closedJet_value_smul]
  calc
    _ ≤ ‖((spatialBasis direction coordinate : ℝ) : ℂ) • field.value‖ +
        ‖(coordinateJet coordinate (partialJet direction field)).value‖ := norm_add_le _ _
    _ ≤ ‖field.value‖ + ‖(partialJet direction field).value‖ := by
      apply add_le_add _ (coordinate_value_norm coordinate _)
      rw [norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg _) coefficient

theorem signedCoordinate_value_norm {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (field : ClosedJet dimension) :
    ‖(coordinateMultiplyJet (mode : ℝ) field).value‖ ≤ 2 * ‖field.value‖ := by
  have coefficient : ‖Complex.I * ((mode : ℝ) : ℂ)‖ = 1 := by rcases center with rfl | rfl <;> norm_num
  rw [centerCoordinate_decomposition, closedJet_value_add, closedJet_value_smul]
  calc
    _ ≤ ‖(coordinateJet 0 field).value‖ + ‖(Complex.I * ((mode : ℝ) : ℂ)) • (coordinateJet 1 field).value‖ := norm_add_le _ _
    _ ≤ ‖field.value‖ + ‖field.value‖ := by
      rw [norm_smul, coefficient, one_mul]
      exact add_le_add (coordinate_value_norm 0 field) (coordinate_value_norm 1 field)
    _ = _ := by ring

theorem signedCoordinate_partial_norm {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (direction : Fin 2) (field : ClosedJet dimension) :
    ‖(partialJet direction (coordinateMultiplyJet (mode : ℝ) field)).value‖ ≤
      2 * (‖field.value‖ + ‖(partialJet direction field).value‖) := by
  have coefficient : ‖Complex.I * ((mode : ℝ) : ℂ)‖ = 1 := by rcases center with rfl | rfl <;> norm_num
  rw [centerCoordinate_decomposition, centerPartial_add, centerPartial_smul, closedJet_value_add, closedJet_value_smul]
  calc
    _ ≤ ‖(partialJet direction (coordinateJet 0 field)).value‖ +
        ‖(Complex.I * ((mode : ℝ) : ℂ)) • (partialJet direction (coordinateJet 1 field)).value‖ := norm_add_le _ _
    _ ≤ (‖field.value‖ + ‖(partialJet direction field).value‖) +
        (‖field.value‖ + ‖(partialJet direction field).value‖) := by
      rw [norm_smul, coefficient, one_mul]
      exact add_le_add (partial_coordinate_value_norm direction 0 field) (partial_coordinate_value_norm direction 1 field)
    _ = _ := by ring

def nativeSupFactor (grade : ℕ) : ℝ :=
  Real.sqrt (Fintype.card (DerivativeIndex grade)) * Real.sqrt ((volume.restrict openUnitDisk).real univ)

theorem nativeSupFactor_nonnegative (grade : ℕ) : 0 ≤ nativeSupFactor grade := by
  unfold nativeSupFactor
  positivity

/-- Every original Cartesian multi-index appears exactly once in the
ordinary Hs norm. This helper only converts supplied C0 row estimates. -/
theorem nativeGrade_of_derivative_sup (grade : ℕ) (field : ClosedJet 1) (bound : ℝ)
    (nonnegative : 0 ≤ bound)
    (bounded : ∀ (order : ℕ), order ≤ grade → ∀ word : CartesianWord order,
      ‖closedDerivative field order word‖ ≤ bound) :
    ‖unitDiskCoreInto grade field‖ ≤ nativeSupFactor grade * bound := by
  rw [unitDiskCore_norm]
  have estimate := apRow_norm_bound_of_coordinates (unitSobolevRow grade field)
    (Real.sqrt ((volume.restrict openUnitDisk).real univ) * bound)
    (mul_nonneg (Real.sqrt_nonneg _) nonnegative) (fun index => by
      rw [unitSobolevRow_coordinate]
      apply (closedValueL2_norm_le (closedMultiDerivative field (derivativeMultiIndex index))).trans
      exact mul_le_mul_of_nonneg_left (bounded _ index.property _) (Real.sqrt_nonneg _))
  exact estimate.trans_eq (mul_assoc _ _ _).symm

theorem nativeFirstGrade_of_sup (field : ClosedJet 1) (bound : ℝ) (nonnegative : 0 ≤ bound)
    (values : ‖field.value‖ ≤ bound)
    (partials : ∀ direction : Fin 2, ‖(partialJet direction field).value‖ ≤ bound) :
    ‖unitDiskCoreInto 1 field‖ ≤ nativeSupFactor 1 * bound := by
  apply nativeGrade_of_derivative_sup 1 field bound nonnegative
  intro order small word
  have alternative : order = 0 ∨ order = 1 := by omega
  rcases alternative with rfl | rfl
  · have empty : word = emptyCartesianWord := Subsingleton.elim _ _
    rw [empty, closedDerivative_zero_order]
    exact values
  · have constant : word = fun _ => word 0 := funext (fun index => congrArg word (Subsingleton.elim index 0))
    rw [constant]
    exact partials (word 0)

end Grad.ActualCenterBounds
