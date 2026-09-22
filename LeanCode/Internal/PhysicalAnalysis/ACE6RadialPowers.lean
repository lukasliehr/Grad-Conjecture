import ACE5CenterQuotientRadiality

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial
open Grad.NonlinearProduct Grad.NonlinearRange Grad.NonlinearQuotientBounds

/-- The literal squared Euclidean radius, expressed polynomially. -/
def radiusSquare (point : SpatialPlane) : ℝ := (point 0) ^ 2 + (point 1) ^ 2

theorem radiusSquare_eq (point : SpatialPlane) : radiusSquare point = ‖point‖ ^ 2 := by
  rw [Grad.NonlinearQuotient.disk_norm_sq]
  rfl

theorem radiusSquare_smooth : ContDiff ℝ ∞ radiusSquare := by
  unfold radiusSquare
  fun_prop

theorem radiusSquare_dilation (scale : ℝ) (point : SpatialPlane) :
    radiusSquare (scale • point) = scale ^ 2 * radiusSquare point := by
  simp only [radiusSquare, PiLp.smul_apply, smul_eq_mul]
  ring

def radiusPowerValue {dimension : ℕ} (power : ℕ) (field : ClosedJet dimension)
    (point : SpatialPlane) : ComplexEuclidean dimension :=
  radiusSquare point ^ power • smoothClosedExtension field point

theorem radiusPowerValue_smooth {dimension : ℕ} (power : ℕ) (field : ClosedJet dimension) :
    ContDiff ℝ ∞ (radiusPowerValue power field) :=
  (radiusSquare_smooth.pow power).smul (smoothClosedExtension_smooth field)

def radiusPowerJet {dimension : ℕ} (power : ℕ) (field : ClosedJet dimension) : ClosedJet dimension :=
  globalClosedJet (radiusPowerValue power field) (radiusPowerValue_smooth power field)

theorem radiusPowerJet_value {dimension : ℕ} (power : ℕ) (field : ClosedJet dimension) (point : ClosedDisk) :
    (radiusPowerJet power field).value point = radiusSquare point.val ^ power • field.value point := by
  change radiusSquare point.val ^ power • smoothClosedExtension field point.val = _
  rw [smoothClosedExtension_value]

theorem radiusPowerJet_zero {dimension : ℕ} (field : ClosedJet dimension) : radiusPowerJet 0 field = field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [radiusPowerJet_value, pow_zero, one_smul]

theorem radiusPowerJet_addPower {dimension : ℕ} (first second : ℕ) (field : ClosedJet dimension) :
    radiusPowerJet first (radiusPowerJet second field) = radiusPowerJet (first + second) field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [radiusPowerJet_value, smul_smul, pow_add]

theorem radiusPowerJet_add {dimension : ℕ} (power : ℕ) (first second : ClosedJet dimension) :
    radiusPowerJet power (first + second) = radiusPowerJet power first + radiusPowerJet power second := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [radiusPowerJet_value, closedJet_value_add, ContinuousMap.add_apply, smul_add]

theorem radiusPowerJet_smul {dimension : ℕ} (power : ℕ) (scalar : ℂ) (field : ClosedJet dimension) :
    radiusPowerJet power (scalar • field) = scalar • radiusPowerJet power field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [radiusPowerJet_value, closedJet_value_smul, ContinuousMap.smul_apply]
  exact smul_comm _ _ _

def radiusPowerLinear (dimension power : ℕ) : ClosedJet dimension →ₗ[ℂ] ClosedJet dimension where
  toFun := radiusPowerJet power
  map_add' := radiusPowerJet_add power
  map_smul' := radiusPowerJet_smul power

/-- Moving the genuine polynomial through a positive dilation kernel raises
its weight by exactly twice the radius power. -/
theorem powerDilation_radiusPower {dimension : ℕ} (weight power : ℕ) (field : ClosedJet dimension) :
    powerDilationJet weight (radiusPowerJet power field) =
      radiusPowerJet power (powerDilationJet (weight + 2 * power) field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [powerDilationJet_value, radiusPowerJet_value, powerDilationJet_value, ← integral_smul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro scale inside
  dsimp only
  have scaledValue := (smoothClosedExtension_value (radiusPowerJet power field)
    (dilationPoint scale inside.1 inside.2 point)).trans (radiusPowerJet_value power field _)
  have originalValue := smoothClosedExtension_value field (dilationPoint scale inside.1 inside.2 point)
  have equality : smoothClosedExtension (radiusPowerJet power field) (scale • point.val) =
      radiusSquare (scale • point.val) ^ power • smoothClosedExtension field (scale • point.val) :=
    scaledValue.trans (congrArg (fun value => radiusSquare (scale • point.val) ^ power • value) originalValue.symm)
  rw [equality, radiusSquare_dilation, mul_pow, smul_smul, smul_smul]
  congr 1
  rw [← pow_mul, pow_add]
  ring

end Grad.ActualCenterVolterra
