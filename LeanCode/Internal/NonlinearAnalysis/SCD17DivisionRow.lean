import SCD16RadialL2
import FC10Extension

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial Grad.BoundaryTrace

abbrev DivisionRow (dimension : ℕ) (lower : ℝ) := lp (fun _ : ℤ × ℤ => RadialL2 dimension lower) 2

def divisionModeLp {dimension : ℕ} (lower : ℝ) (power radial : ℕ)
    (parameters : PhaseParameters) (field : ACore parameters dimension) (mode : ℤ × ℤ) : RadialL2 dimension lower :=
  ((annularFrequency mode.1 mode.2 : ℂ) ^ power) •
    radialToLp lower
      (radialCoefficientJet (dividedPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2))) mode.1 radial)
      ((radialCoefficientJet_smooth _ (dividedPolarValue_smooth _) _ _).continuous)

theorem divisionModeLp_norm_sq {dimension : ℕ} (lower : ℝ)
    (nonnegative : 0 ≤ lower) (bounded : lower ≤ 1) (power radial : ℕ)
    (parameters : PhaseParameters) (field : ACore parameters dimension) (mode : ℤ × ℤ) :
    ‖divisionModeLp lower power radial parameters field mode‖ ^ 2 =
      originalDivisionEnergy lower power radial parameters field mode := by
  rw [divisionModeLp, norm_smul, Complex.norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (annularFrequency_nonnegative _ _), mul_pow,
    radialToLp_norm_sq lower nonnegative bounded]
  unfold originalDivisionEnergy radialModeEnergy
  rw [← pow_mul, Nat.mul_comm power 2]

theorem divisionModeLp_add {dimension : ℕ} (lower : ℝ) (positive : 0 < lower)
    (power radial : ℕ) (parameters : PhaseParameters) (first second : ACore parameters dimension) (mode : ℤ × ℤ) :
    divisionModeLp lower power radial parameters (first + second) mode =
      divisionModeLp lower power radial parameters first mode + divisionModeLp lower power radial parameters second mode := by
  unfold divisionModeLp
  rw [radialToLp_add_of_interior lower positive]
  · exact smul_add _ _ _
  · intro radius inside
    exact weightedDividedCoefficient_add parameters mode.2 (first.val mode.2) (second.val mode.2) mode.1 radial radius inside

theorem divisionModeLp_smul {dimension : ℕ} (lower : ℝ) (positive : 0 < lower)
    (power radial : ℕ) (parameters : PhaseParameters) (scalar : ℂ) (field : ACore parameters dimension) (mode : ℤ × ℤ) :
    divisionModeLp lower power radial parameters (scalar • field) mode =
      scalar • divisionModeLp lower power radial parameters field mode := by
  unfold divisionModeLp
  rw [radialToLp_smul_of_interior lower positive scalar]
  · exact smul_comm _ _ _
  · intro radius inside
    exact weightedDividedCoefficient_smul parameters mode.2 scalar (field.val mode.2) mode.1 radial radius inside

theorem divisionModeLp_memlp {dimension grade power radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (field : ACore parameters dimension) (paid : power + radial + 3 ≤ grade) :
    Memℓp (divisionModeLp lower power radial parameters field) 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  simp_rw [divisionModeLp_norm_sq lower positive.le bounded]
  exact original_division_summable parameters field paid lower positive.le bounded

def coreDivisionRowLinear {dimension grade power radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + radial + 3 ≤ grade) :
    GradeCore parameters dimension grade →ₗ[ℂ] DivisionRow dimension lower where
  toFun field := ⟨divisionModeLp lower power radial parameters field.toCore,
    divisionModeLp_memlp lower positive bounded parameters field.toCore paid⟩
  map_add' first second := by
    apply Subtype.ext
    funext mode
    exact divisionModeLp_add lower positive power radial parameters first.toCore second.toCore mode
  map_smul' scalar field := by
    apply Subtype.ext
    funext mode
    exact divisionModeLp_smul lower positive power radial parameters scalar field.toCore mode

theorem coreDivisionRow_norm_sq {dimension grade power radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + radial + 3 ≤ grade) (field : GradeCore parameters dimension grade) :
    ‖coreDivisionRowLinear lower positive bounded parameters paid field‖ ^ 2 =
      ∑' mode : ℤ × ℤ, originalDivisionEnergy lower power radial parameters field.toCore mode := by
  have equality := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (coreDivisionRowLinear lower positive bounded parameters paid field)
  norm_num at equality
  rw [equality]
  apply tsum_congr
  intro mode
  exact divisionModeLp_norm_sq lower positive.le bounded power radial parameters field.toCore mode

theorem coreDivisionRow_norm_bound {dimension grade power radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + radial + 3 ≤ grade) (field : GradeCore parameters dimension grade) :
    ‖coreDivisionRowLinear lower positive bounded parameters paid field‖ ≤
      Real.sqrt (finiteAngularBoundConstant power radial) * ‖field‖ := by
  have energy := original_division_energy_bound parameters field.toCore paid lower positive.le bounded
  rw [← coreDivisionRow_norm_sq lower positive bounded parameters paid, GradeCore.ofCore_toCore] at energy
  have roots := Real.sqrt_le_sqrt energy
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_mul (finiteAngularBoundConstant_nonnegative _ _)] using roots

end Grad.SourceCollarDivision
