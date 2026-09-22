import BKA1TraceCarriers
import BL41WeightRatios
import PA5PhaseConsumer

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift
open Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace
open Grad.PhaseAlgebra

def twoFrequencyTranslation (shift : ℤ × ℤ) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun mode := (mode.1 - shift.1, mode.2 - shift.2)
  invFun mode := (mode.1 + shift.1, mode.2 + shift.2)
  left_inv mode := by simp
  right_inv mode := by simp

@[simp] theorem twoFrequencyTranslation_apply (shift mode : ℤ × ℤ) :
    twoFrequencyTranslation shift mode =
      (mode.1 - shift.1, mode.2 - shift.2) := rfl

theorem annularFrequency_one_le (mode : ℤ × ℤ) :
    1 ≤ annularFrequency mode.1 mode.2 := by
  unfold annularFrequency
  linarith [abs_nonneg (mode.1 : ℝ), abs_nonneg (mode.2 : ℝ)]

theorem annularFrequency_sub_le_mul (mode shift : ℤ × ℤ) :
    annularFrequency (mode.1 - shift.1) (mode.2 - shift.2) ≤
      annularFrequency mode.1 mode.2 * annularFrequency shift.1 shift.2 := by
  have first := abs_sub (mode.1 : ℝ) (shift.1 : ℝ)
  have second := abs_sub (mode.2 : ℝ) (shift.2 : ℝ)
  have modeOne := annularFrequency_one_le mode
  have shiftSum : 0 ≤ |(shift.1 : ℝ)| + |(shift.2 : ℝ)| := by positivity
  have absorbed := mul_le_mul_of_nonneg_right modeOne shiftSum
  calc
    annularFrequency (mode.1 - shift.1) (mode.2 - shift.2)
        ≤ annularFrequency mode.1 mode.2 +
            (|(shift.1 : ℝ)| + |(shift.2 : ℝ)|) := by
          unfold annularFrequency
          push_cast
          linarith
    _ ≤ annularFrequency mode.1 mode.2 +
          annularFrequency mode.1 mode.2 *
            (|(shift.1 : ℝ)| + |(shift.2 : ℝ)|) := by
          have absorbed' : |(shift.1 : ℝ)| + |(shift.2 : ℝ)| ≤
              annularFrequency mode.1 mode.2 *
                (|(shift.1 : ℝ)| + |(shift.2 : ℝ)|) := by
            simpa only [one_mul] using absorbed
          simpa only [add_comm] using
            add_le_add_left absorbed' (annularFrequency mode.1 mode.2)
    _ = annularFrequency mode.1 mode.2 *
          annularFrequency shift.1 shift.2 := by
          unfold annularFrequency
          ring

theorem one_add_abs_shift_le (value shift : ℤ) :
    1 + |(value : ℝ)| ≤
      (1 + |(shift : ℝ)|) * (1 + |((value - shift : ℤ) : ℝ)|) := by
  have triangle : |(value : ℝ)| ≤
      |((value - shift : ℤ) : ℝ)| + |(shift : ℝ)| := by
    calc
      |(value : ℝ)| = |(((value - shift : ℤ) : ℝ) + (shift : ℝ))| := by
        congr 1
        push_cast
        ring
      _ ≤ |((value - shift : ℤ) : ℝ)| + |(shift : ℝ)| := abs_add_le _ _
  nlinarith [abs_nonneg (shift : ℝ),
    abs_nonneg ((value - shift : ℤ) : ℝ)]

theorem splitTangentialWeight_shift_le (angular cell : ℕ)
    (mode shift : ℤ × ℤ) :
    splitTangentialWeight angular cell mode ≤
      annularFrequency shift.1 shift.2 ^ (angular + cell) *
        splitTangentialWeight angular cell (twoFrequencyTranslation shift mode) := by
  have angularBound := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |(mode.1 : ℝ)|)
    (one_add_abs_shift_le mode.1 shift.1) angular
  have cellBound := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |(mode.2 : ℝ)|)
    (one_add_abs_shift_le mode.2 shift.2) cell
  rw [mul_pow] at angularBound cellBound
  have shiftAngular : (1 + |(shift.1 : ℝ)|) ≤
      annularFrequency shift.1 shift.2 := by
    unfold annularFrequency
    linarith [abs_nonneg (shift.2 : ℝ)]
  have shiftCell : (1 + |(shift.2 : ℝ)|) ≤
      annularFrequency shift.1 shift.2 := by
    unfold annularFrequency
    linarith [abs_nonneg (shift.1 : ℝ)]
  have angularShiftPow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |(shift.1 : ℝ)|)
    shiftAngular angular
  have cellShiftPow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |(shift.2 : ℝ)|)
    shiftCell cell
  unfold splitTangentialWeight
  simp only [twoFrequencyTranslation_apply]
  calc
    (1 + |(mode.1 : ℝ)|) ^ angular * (1 + |(mode.2 : ℝ)|) ^ cell
        ≤ ((1 + |(shift.1 : ℝ)|) ^ angular *
              (1 + |((mode.1 - shift.1 : ℤ) : ℝ)|) ^ angular) *
            ((1 + |(shift.2 : ℝ)|) ^ cell *
              (1 + |((mode.2 - shift.2 : ℤ) : ℝ)|) ^ cell) :=
          mul_le_mul angularBound cellBound (pow_nonneg (by positivity) _)
            (mul_nonneg (pow_nonneg (by positivity) _)
              (pow_nonneg (by positivity) _))
    _ = ((1 + |(shift.1 : ℝ)|) ^ angular *
            (1 + |(shift.2 : ℝ)|) ^ cell) *
          ((1 + |((mode.1 - shift.1 : ℤ) : ℝ)|) ^ angular *
            (1 + |((mode.2 - shift.2 : ℤ) : ℝ)|) ^ cell) := by ring
    _ ≤ (annularFrequency shift.1 shift.2 ^ angular *
            annularFrequency shift.1 shift.2 ^ cell) *
          ((1 + |((mode.1 - shift.1 : ℤ) : ℝ)|) ^ angular *
            (1 + |((mode.2 - shift.2 : ℤ) : ℝ)|) ^ cell) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul angularShiftPow cellShiftPow (pow_nonneg (by positivity) _)
              (pow_nonneg (annularFrequency_pos shift).le _))
            (mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (by positivity) _))
    _ = annularFrequency shift.1 shift.2 ^ (angular + cell) *
          ((1 + |((mode.1 - shift.1 : ℤ) : ℝ)|) ^ angular *
            (1 + |((mode.2 - shift.2 : ℤ) : ℝ)|) ^ cell) := by
          rw [pow_add]

theorem negativeHalfRatio_le_frequency (mode shift : ℤ × ℤ) :
    Real.sqrt (annularFrequency (mode.1 - shift.1) (mode.2 - shift.2) /
      annularFrequency mode.1 mode.2) ≤ annularFrequency shift.1 shift.2 := by
  have ratioBound : annularFrequency (mode.1 - shift.1) (mode.2 - shift.2) /
      annularFrequency mode.1 mode.2 ≤ annularFrequency shift.1 shift.2 := by
    rw [div_le_iff₀ (annularFrequency_pos mode)]
    simpa only [mul_comm] using annularFrequency_sub_le_mul mode shift
  calc
    Real.sqrt (annularFrequency (mode.1 - shift.1) (mode.2 - shift.2) /
        annularFrequency mode.1 mode.2)
        ≤ Real.sqrt (annularFrequency shift.1 shift.2) :=
          Real.sqrt_le_sqrt ratioBound
    _ ≤ annularFrequency shift.1 shift.2 := by
      rw [Real.sqrt_le_iff]
      exact ⟨(annularFrequency_one_le shift).trans' zero_le_one,
        (show annularFrequency shift.1 shift.2 ≤
          annularFrequency shift.1 shift.2 ^ 2 by
            simpa only [pow_two, one_mul] using
              mul_le_mul_of_nonneg_right (annularFrequency_one_le shift)
                (annularFrequency_pos shift).le)⟩

def boundaryCoefficientPhaseCost (parameters : PhaseParameters) (shift : ℤ × ℤ) : ℝ :=
  Real.exp (parameters.sigma0 + parameters.gamma) *
    phaseWeight parameters 1 shift.2

theorem boundaryCoefficientPhaseCost_nonnegative (parameters : PhaseParameters)
    (shift : ℤ × ℤ) : 0 ≤ boundaryCoefficientPhaseCost parameters shift := by
  unfold boundaryCoefficientPhaseCost
  exact mul_nonneg (Real.exp_pos _).le
    (phaseWeight_pos parameters 1 shift.2).le

def negativeShiftCost (parameters : PhaseParameters) (angular cell : ℕ)
    (shift : ℤ × ℤ) : ℝ :=
  boundaryCoefficientPhaseCost parameters shift *
    annularFrequency shift.1 shift.2 ^ (angular + cell + 1)

theorem negativeShiftCost_nonnegative (parameters : PhaseParameters) (angular cell : ℕ)
    (shift : ℤ × ℤ) : 0 ≤ negativeShiftCost parameters angular cell shift := by
  unfold negativeShiftCost
  exact mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters shift)
    (pow_nonneg (annularFrequency_pos shift).le _)

private theorem boundaryPhase_eq_radialPhase_one (parameters : PhaseParameters) (cell : ℤ) :
    boundaryPhase parameters cell = radialPhase parameters 1 cell := by
  unfold boundaryPhase radialPhase
  simp only [one_pow, mul_one]

private theorem negativeTraceWeightSq_factor (parameters : PhaseParameters)
    (angular cell : ℕ) (mode : ℤ × ℤ) :
    negativeTraceWeightSq parameters angular cell mode =
      Real.exp (2 * boundaryPhase parameters mode.2) *
        splitTangentialWeight angular cell mode ^ 2 *
          (annularFrequency mode.1 mode.2)⁻¹ := by
  unfold negativeTraceWeightSq splitTangentialWeight
  rw [mul_pow]
  rw [show 2 * angular = angular * 2 by omega,
    show 2 * cell = cell * 2 by omega, pow_mul, pow_mul]
  ring

private theorem negativeHalfInverse_shift_le (mode shift : ℤ × ℤ) :
    (annularFrequency mode.1 mode.2)⁻¹ ≤
      annularFrequency shift.1 shift.2 ^ 2 *
        (annularFrequency (mode.1 - shift.1) (mode.2 - shift.2))⁻¹ := by
  have ratioSq := pow_le_pow_left₀
    (Real.sqrt_nonneg
      (annularFrequency (mode.1 - shift.1) (mode.2 - shift.2) /
        annularFrequency mode.1 mode.2))
    (negativeHalfRatio_le_frequency mode shift) 2
  rw [Real.sq_sqrt (div_nonneg
    (annularFrequency_pos
      (mode.1 - shift.1, mode.2 - shift.2)).le
    (annularFrequency_pos mode).le)] at ratioSq
  have factorization :
      (annularFrequency mode.1 mode.2)⁻¹ =
        (annularFrequency (mode.1 - shift.1) (mode.2 - shift.2) /
          annularFrequency mode.1 mode.2) *
        (annularFrequency (mode.1 - shift.1) (mode.2 - shift.2))⁻¹ := by
    have inputNe : annularFrequency (mode.1 - shift.1) (mode.2 - shift.2) ≠ 0 :=
      (annularFrequency_pos (twoFrequencyTranslation shift mode)).ne'
    calc
      (annularFrequency mode.1 mode.2)⁻¹ =
          (annularFrequency (mode.1 - shift.1) (mode.2 - shift.2) *
            (annularFrequency (mode.1 - shift.1) (mode.2 - shift.2))⁻¹) *
              (annularFrequency mode.1 mode.2)⁻¹ := by rw [mul_inv_cancel₀ inputNe, one_mul]
      _ = _ := by rw [div_eq_mul_inv]; ring
  rw [factorization]
  exact mul_le_mul_of_nonneg_right ratioSq
    (inv_nonneg.mpr
      (annularFrequency_pos (twoFrequencyTranslation shift mode)).le)

/-- The exact AH17 weight-ratio consequence with one whole displacement
moment paying the negative half order. -/
theorem negativeTraceWeight_shift_le (parameters : PhaseParameters) (angular cell : ℕ)
    (mode shift : ℤ × ℤ) :
    negativeTraceWeight parameters angular cell mode ≤
      negativeShiftCost parameters angular cell shift *
        negativeTraceWeight parameters angular cell (twoFrequencyTranslation shift mode) := by
  let input := twoFrequencyTranslation shift mode
  let displacement := annularFrequency shift.1 shift.2
  let phaseCost := boundaryCoefficientPhaseCost parameters shift
  have phaseBase :
      Real.exp (boundaryPhase parameters mode.2) ≤
        phaseCost * Real.exp (boundaryPhase parameters input.2) := by
    have ratio := exp_radialPhase_ratio parameters 1 zero_le_one le_rfl mode.2 input.2
    have envelope := exp_radialPhase_le parameters 1 zero_le_one le_rfl shift.2
    have inputCell : mode.2 - input.2 = shift.2 := by
      dsimp only [input]
      rw [twoFrequencyTranslation_apply]
      simp only [sub_sub_cancel]
    rw [boundaryPhase_eq_radialPhase_one, boundaryPhase_eq_radialPhase_one]
    calc
      Real.exp (radialPhase parameters 1 mode.2) =
          Real.exp (radialPhase parameters 1 mode.2 -
            radialPhase parameters 1 input.2) *
            Real.exp (radialPhase parameters 1 input.2) := by
              rw [← Real.exp_add]
              congr 1
              ring
      _ ≤ Real.exp (radialPhase parameters 1 (mode.2 - input.2)) *
            Real.exp (radialPhase parameters 1 input.2) :=
          mul_le_mul_of_nonneg_right ratio (Real.exp_pos _).le
      _ = Real.exp (radialPhase parameters 1 shift.2) *
            Real.exp (radialPhase parameters 1 input.2) := by rw [inputCell]
      _ ≤ (Real.exp (parameters.sigma0 + parameters.gamma) *
            phaseWeight parameters 1 shift.2) *
            Real.exp (radialPhase parameters 1 input.2) :=
          mul_le_mul_of_nonneg_right envelope (Real.exp_pos _).le
      _ = phaseCost * Real.exp (radialPhase parameters 1 input.2) := rfl
  have phaseSq :
      Real.exp (2 * boundaryPhase parameters mode.2) ≤
        phaseCost ^ 2 * Real.exp (2 * boundaryPhase parameters input.2) := by
    have squared := pow_le_pow_left₀ (Real.exp_pos _).le phaseBase 2
    calc
      Real.exp (2 * boundaryPhase parameters mode.2)
          = Real.exp (boundaryPhase parameters mode.2) ^ 2 := by
              rw [pow_two, two_mul, Real.exp_add]
      _ ≤ (phaseCost * Real.exp (boundaryPhase parameters input.2)) ^ 2 := squared
      _ = phaseCost ^ 2 * Real.exp (2 * boundaryPhase parameters input.2) := by
              rw [mul_pow, pow_two, two_mul, Real.exp_add]
              ring
  have splitSq :
      splitTangentialWeight angular cell mode ^ 2 ≤
        displacement ^ (2 * (angular + cell)) *
          splitTangentialWeight angular cell input ^ 2 := by
    have splitBase := splitTangentialWeight_shift_le angular cell mode shift
    have squared := pow_le_pow_left₀
      (splitTangentialWeight_pos angular cell mode).le splitBase 2
    calc
      splitTangentialWeight angular cell mode ^ 2
          ≤ (displacement ^ (angular + cell) *
              splitTangentialWeight angular cell input) ^ 2 := squared
      _ = displacement ^ (2 * (angular + cell)) *
            splitTangentialWeight angular cell input ^ 2 := by
              rw [mul_pow, ← pow_mul]
              congr 2
              omega
  have inversePart :
      (annularFrequency mode.1 mode.2)⁻¹ ≤
        displacement ^ 2 *
          (annularFrequency input.1 input.2)⁻¹ := by
    dsimp only [displacement, input]
    simpa only [twoFrequencyTranslation_apply] using
      negativeHalfInverse_shift_le mode shift
  have squareBound :
      negativeTraceWeightSq parameters angular cell mode ≤
        negativeShiftCost parameters angular cell shift ^ 2 *
          negativeTraceWeightSq parameters angular cell input := by
    have displacementPower :
        displacement ^ (2 * (angular + cell)) * displacement ^ 2 =
          (displacement ^ (angular + cell + 1)) ^ 2 := by
      calc
        displacement ^ (2 * (angular + cell)) * displacement ^ 2 =
            displacement ^ (2 * (angular + cell) + 2) := by rw [pow_add]
        _ = displacement ^ ((angular + cell + 1) * 2) := by
            congr 1
            omega
        _ = (displacement ^ (angular + cell + 1)) ^ 2 := by rw [pow_mul]
    rw [negativeTraceWeightSq_factor, negativeTraceWeightSq_factor]
    calc
      Real.exp (2 * boundaryPhase parameters mode.2) *
            splitTangentialWeight angular cell mode ^ 2 *
          (annularFrequency mode.1 mode.2)⁻¹
          ≤ (phaseCost ^ 2 * Real.exp (2 * boundaryPhase parameters input.2)) *
              (displacement ^ (2 * (angular + cell)) *
                splitTangentialWeight angular cell input ^ 2) *
              (displacement ^ 2 * (annularFrequency input.1 input.2)⁻¹) := by
            exact mul_le_mul
              (mul_le_mul phaseSq splitSq
                (sq_nonneg _) (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))
              inversePart (inv_nonneg.mpr (annularFrequency_pos mode).le)
              (mul_nonneg
                (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
                (mul_nonneg (pow_nonneg (annularFrequency_pos shift).le _)
                  (sq_nonneg _)))
      _ = negativeShiftCost parameters angular cell shift ^ 2 *
            (Real.exp (2 * boundaryPhase parameters input.2) *
              splitTangentialWeight angular cell input ^ 2 *
                (annularFrequency input.1 input.2)⁻¹) := by
            unfold negativeShiftCost
            dsimp only [phaseCost, displacement]
            rw [mul_pow]
            rw [← displacementPower]
            ring
  apply (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (negativeShiftCost_nonnegative parameters angular cell shift)
      (Real.sqrt_nonneg _))).mp
  change Real.sqrt (negativeTraceWeightSq parameters angular cell mode) ^ 2 ≤
    (negativeShiftCost parameters angular cell shift *
      Real.sqrt (negativeTraceWeightSq parameters angular cell input)) ^ 2
  rw [Real.sq_sqrt (negativeTraceWeightSq_pos parameters angular cell mode).le,
    mul_pow,
    Real.sq_sqrt
      (negativeTraceWeightSq_pos parameters angular cell input).le]
  exact squareBound

end Grad.BoundaryKernelAction
