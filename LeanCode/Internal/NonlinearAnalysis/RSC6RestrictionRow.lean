import RSC5PolarLinearity
import FC10Extension

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.SourceCollarRestriction

open Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial Grad.BoundaryTrace

def restrictionModeLp {dimension : ℕ} (lower : ℝ) (power radial : ℕ)
    (parameters : PhaseParameters) (field : ACore parameters dimension) (mode : ℤ × ℤ) : RadialL2 dimension lower :=
  ((annularFrequency mode.1 mode.2 : ℂ) ^ power) •
    radialToLp lower
      (radialCoefficientJet (originalPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2))) mode.1 radial)
      ((radialCoefficientJet_smooth _ (originalPolarValue_smooth _) _ _).continuous)

theorem restrictionModeLp_norm_sq {dimension : ℕ} (lower : ℝ)
    (nonnegative : 0 ≤ lower) (bounded : lower ≤ 1) (power radial : ℕ)
    (parameters : PhaseParameters) (field : ACore parameters dimension) (mode : ℤ × ℤ) :
    ‖restrictionModeLp lower power radial parameters field mode‖ ^ 2 =
      originalRestrictionEnergy lower power radial parameters field mode := by
  rw [restrictionModeLp, norm_smul, Complex.norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (annularFrequency_nonnegative _ _), mul_pow,
    radialToLp_norm_sq lower nonnegative bounded]
  unfold originalRestrictionEnergy restrictionModeEnergy annularCoefficientEnergy
  rw [← pow_mul, Nat.mul_comm power 2]
  rfl

theorem restrictionModeLp_add {dimension : ℕ} (lower : ℝ) (positive : 0 < lower)
    (power radial : ℕ) (parameters : PhaseParameters) (first second : ACore parameters dimension) (mode : ℤ × ℤ) :
    restrictionModeLp lower power radial parameters (first + second) mode =
      restrictionModeLp lower power radial parameters first mode + restrictionModeLp lower power radial parameters second mode := by
  unfold restrictionModeLp
  rw [radialToLp_add_of_interior lower positive]
  · exact smul_add _ _ _
  · intro radius inside
    exact weightedPolarCoefficient_add parameters mode.2 (first.val mode.2) (second.val mode.2) mode.1 radial radius inside

theorem restrictionModeLp_smul {dimension : ℕ} (lower : ℝ) (positive : 0 < lower)
    (power radial : ℕ) (parameters : PhaseParameters) (scalar : ℂ) (field : ACore parameters dimension) (mode : ℤ × ℤ) :
    restrictionModeLp lower power radial parameters (scalar • field) mode =
      scalar • restrictionModeLp lower power radial parameters field mode := by
  unfold restrictionModeLp
  rw [radialToLp_smul_of_interior lower positive scalar]
  · exact smul_comm _ _ _
  · intro radius inside
    exact weightedPolarCoefficient_smul parameters mode.2 scalar (field.val mode.2) mode.1 radial radius inside

theorem restrictionModeLp_memlp {dimension grade power radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (field : ACore parameters dimension) (paid : power + radial ≤ grade) :
    Memℓp (restrictionModeLp lower power radial parameters field) 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  simp_rw [restrictionModeLp_norm_sq lower positive.le bounded]
  exact original_restriction_summable parameters field paid lower positive.le bounded

def coreRestrictionRowLinear {dimension grade power radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + radial ≤ grade) :
    GradeCore parameters dimension grade →ₗ[ℂ] DivisionRow dimension lower where
  toFun field := ⟨restrictionModeLp lower power radial parameters field.toCore,
    restrictionModeLp_memlp lower positive bounded parameters field.toCore paid⟩
  map_add' first second := by
    apply Subtype.ext
    funext mode
    exact restrictionModeLp_add lower positive power radial parameters first.toCore second.toCore mode
  map_smul' scalar field := by
    apply Subtype.ext
    funext mode
    exact restrictionModeLp_smul lower positive power radial parameters scalar field.toCore mode

theorem coreRestrictionRow_norm_sq {dimension grade power radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + radial ≤ grade) (field : GradeCore parameters dimension grade) :
    ‖coreRestrictionRowLinear lower positive bounded parameters paid field‖ ^ 2 =
      ∑' mode : ℤ × ℤ, originalRestrictionEnergy lower power radial parameters field.toCore mode := by
  have equality := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (coreRestrictionRowLinear lower positive bounded parameters paid field)
  norm_num at equality
  rw [equality]
  apply tsum_congr
  intro mode
  exact restrictionModeLp_norm_sq lower positive.le bounded power radial parameters field.toCore mode

theorem coreRestrictionRow_norm_bound {dimension grade power radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + radial ≤ grade) (field : GradeCore parameters dimension grade) :
    ‖coreRestrictionRowLinear lower positive bounded parameters paid field‖ ≤
      Real.sqrt (restrictionRowConstant power radial) * ‖field‖ := by
  have energy := original_restriction_energy_bound parameters field.toCore paid lower positive.le bounded
  rw [← coreRestrictionRow_norm_sq lower positive bounded parameters paid, GradeCore.ofCore_toCore] at energy
  have roots := Real.sqrt_le_sqrt energy
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_mul (restrictionRowConstant_nonnegative _ _)] using roots

end Grad.SourceCollarRestriction
