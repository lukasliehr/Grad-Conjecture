import AKN8ActualTiltedBulkEnergy
import SCD17DivisionRow

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.ExhaustionSourceAllocation

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.SourceCollarDivision
open Grad.NonlinearRadial Grad.BoundaryTrace

def sourceTiltFactor (lower : ℝ) (division : ℕ) (radius : ℝ) : ℝ :=
  (max lower radius) ^ (-9 / 4 - (division : ℝ))

theorem sourceTiltFactor_continuous (lower : ℝ) (positive : 0 < lower) (division : ℕ) :
    Continuous (sourceTiltFactor lower division) :=
  (continuous_const.max continuous_id).rpow_const
    (fun radius => Or.inl (positive.trans_le (le_max_left lower radius)).ne')

theorem sourceTiltFactor_square (lower radius : ℝ) (positive : 0 < lower)
    (inside : lower ≤ radius) (division : ℕ) :
    radius * sourceTiltFactor lower division radius ^ 2 = sourceTiltDensity lower division radius := by
  have radialPositive := positive.trans_le inside
  simp only [sourceTiltFactor, sourceTiltDensity, max_eq_right inside]
  rw [pow_two, ← Real.rpow_add radialPositive]
  conv_lhs => lhs; rw [← Real.rpow_one radius]
  rw [← Real.rpow_add radialPositive]
  congr 1
  ring

def sourceTiltRadialValue {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) (lower : ℝ) (division : ℕ) (mode : ℤ) (radius : ℝ) : ComplexEuclidean dimension :=
  sourceTiltFactor lower division radius • sourceCircleCoefficient parameters cell field radius mode

theorem sourceTiltRadialValue_continuous {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) (lower : ℝ) (positive : 0 < lower) (division : ℕ) (mode : ℤ) :
    Continuous (sourceTiltRadialValue parameters cell field lower division mode) :=
  (sourceTiltFactor_continuous lower positive division).smul (sourceCircleCoefficient_continuous parameters cell field mode)

def sourceTiltModeLp {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
    (lower : ℝ) (positive : 0 < lower) (division power : ℕ) (mode : ℤ × ℤ) : RadialL2 dimension lower :=
  ((annularFrequency mode.1 mode.2 : ℂ) ^ power) • radialToLp lower
    (sourceTiltRadialValue parameters mode.2 (field.val mode.2) lower division mode.1)
    (sourceTiltRadialValue_continuous parameters mode.2 (field.val mode.2) lower positive division mode.1)

theorem sourceTiltModeLp_norm_sq {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (division power : ℕ) (mode : ℤ × ℤ) :
    ‖sourceTiltModeLp parameters field lower positive division power mode‖ ^ 2 =
      sourceTiltModeEnergy parameters lower division power field mode := by
  rw [sourceTiltModeLp, norm_smul, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (annularFrequency_nonnegative _ _), mul_pow, radialToLp_norm_sq lower positive.le bounded,
    ← pow_mul, Nat.mul_comm power 2, sourceTiltModeEnergy, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro radius member
  have inside : radius ∈ Icc lower 1 := by simpa only [uIcc_of_le bounded] using member
  have scalarNonnegative : 0 ≤ sourceTiltFactor lower division radius :=
    Real.rpow_nonneg (positive.trans_le (le_max_left _ _)).le _
  simp only [sourceTiltRadialValue, norm_smul, Real.norm_eq_abs, abs_of_nonneg scalarNonnegative, mul_pow]
  have scalar := sourceTiltFactor_square lower radius positive inside.1 division
  simp only [sourceCircleEnergy]
  rw [← scalar]
  ring

theorem sourceTiltModeLp_memlp {dimension grade depth power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (flat : ∀ cell, VanishingJets depth (field.val cell)) (paid : depth + power + 2 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (division : ℕ) (vanishing : division + 2 ≤ depth) :
    Memℓp (sourceTiltModeLp parameters field lower positive division power) 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  simp_rw [sourceTiltModeLp_norm_sq parameters field lower positive bounded]
  exact summable_of_sum_le (sourceTiltModeEnergy_nonnegative parameters lower positive bounded division power field)
    (finite_sourceTilt_bound parameters field flat paid lower positive bounded division vanishing)

/-- The full BF bulk Hilbert row of the same Cartesian field, with actual
r^(-9/4) tilt and optional division by r; no angular projection is inserted. -/
def sourceTiltRow {dimension grade depth power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (flat : ∀ cell, VanishingJets depth (field.val cell)) (paid : depth + power + 2 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (division : ℕ) (vanishing : division + 2 ≤ depth) : DivisionRow dimension lower :=
  ⟨sourceTiltModeLp parameters field lower positive division power,
    sourceTiltModeLp_memlp parameters field flat paid lower positive bounded division vanishing⟩

theorem sourceTiltRow_norm_sq {dimension grade depth power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (flat : ∀ cell, VanishingJets depth (field.val cell)) (paid : depth + power + 2 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (division : ℕ) (vanishing : division + 2 ≤ depth) :
    ‖sourceTiltRow parameters field flat paid lower positive bounded division vanishing‖ ^ 2 =
      ∑' mode : ℤ × ℤ, sourceTiltModeEnergy parameters lower division power field mode := by
  have equality := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (sourceTiltRow parameters field flat paid lower positive bounded division vanishing)
  norm_num at equality
  rw [equality]
  apply tsum_congr
  intro mode
  exact sourceTiltModeLp_norm_sq parameters field lower positive bounded division power mode

theorem sourceTiltRow_bound {dimension grade depth power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (flat : ∀ cell, VanishingJets depth (field.val cell)) (paid : depth + power + 2 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (division : ℕ) (vanishing : division + 2 ≤ depth) :
    ‖sourceTiltRow parameters field flat paid lower positive bounded division vanishing‖ ≤
      Real.sqrt (remainderAngularBoundConstant depth power 0) * ‖GradeCore.ofCoreLinear (grade := grade) field‖ := by
  have energy := full_sourceTilt_bound parameters field flat paid lower positive bounded division vanishing
  rw [← sourceTiltRow_norm_sq parameters field flat paid lower positive bounded division vanishing] at energy
  have roots := Real.sqrt_le_sqrt energy
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_mul (remainderAngularBoundConstant_nonnegative _ _ _)] using roots

end Grad.ExhaustionSourceAllocation
