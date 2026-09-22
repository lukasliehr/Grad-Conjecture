import BLInterface

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SmoothingFamily

def radialBoundaryPhaseDifference (parameters : PhaseParameters) (cell : ℤ) (time : ℝ) : ℝ :=
  parameters.gamma * (Real.sqrt (1 + cellFrequency cell ^ 2) -
    Real.sqrt (1 + (cellFrequency cell * (1 - time)) ^ 2))

theorem radialBoundaryPhaseDifference_bounds (parameters : PhaseParameters) (cell : ℤ)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (timeBound : time ≤ 1) :
    0 ≤ radialBoundaryPhaseDifference parameters cell time ∧
      radialBoundaryPhaseDifference parameters cell time ≤ parameters.gamma * cellFrequency cell * time := by
  have radialNonnegative : 0 ≤ cellFrequency cell * (1 - time) :=
    mul_nonneg (cellFrequency_pos cell).le (sub_nonneg.mpr timeBound)
  have radialBound : cellFrequency cell * (1 - time) ≤ cellFrequency cell := by
    nlinarith [mul_nonneg (cellFrequency_pos cell).le timeNonnegative]
  have increment := Grad.AnalyticWeights.sqrt_increment_bound _ _ radialNonnegative radialBound
  have orderedRoots : Real.sqrt (1 + (cellFrequency cell * (1 - time)) ^ 2) ≤
      Real.sqrt (1 + cellFrequency cell ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [pow_le_pow_left₀ radialNonnegative radialBound 2])
  constructor
  · exact mul_nonneg parameters.gamma_pos.le (sub_nonneg.mpr orderedRoots)
  · have bound := mul_le_mul_of_nonneg_left increment parameters.gamma_pos.le
    unfold radialBoundaryPhaseDifference
    nlinarith

theorem cellFrequency_le_boundaryFrequency (mode : ℤ × ℤ) :
    cellFrequency mode.2 ≤ boundaryFrequency mode := by
  rw [cellFrequency_formula, boundaryFrequency]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (mode.1 : ℝ)])

def boundaryDecayRate (parameters : PhaseParameters) : ℝ := 1 - parameters.gamma

theorem boundaryDecayRate_pos (parameters : PhaseParameters) : 0 < boundaryDecayRate parameters :=
  sub_pos.mpr (parameters_gamma_lt_one parameters)

def conjugatedExponentialProfile (parameters : PhaseParameters) (mode : ℤ × ℤ) (time : ℝ) : ℝ :=
  Real.exp (-boundaryFrequency mode * time + radialBoundaryPhaseDifference parameters mode.2 time)

theorem conjugatedExponentialProfile_decay (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (timeBound : time ≤ 1) :
    conjugatedExponentialProfile parameters mode time ≤
      Real.exp (-boundaryDecayRate parameters * boundaryFrequency mode * time) := by
  apply Real.exp_le_exp.mpr
  have phaseBound := (radialBoundaryPhaseDifference_bounds parameters mode.2 time timeNonnegative timeBound).2
  have frequencyBound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (cellFrequency_le_boundaryFrequency mode) parameters.gamma_pos.le) timeNonnegative
  unfold boundaryDecayRate
  nlinarith

theorem collarCutoff1D_range (time : ℝ) : 0 ≤ collarCutoff1D time ∧ collarCutoff1D time ≤ 1 := by
  constructor
  · exact mul_nonneg (eta_range _).1 (eta_range _).1
  · exact mul_le_one₀ (eta_range _).2 (eta_range _).1 (eta_range _).2

def conjugatedProfile (parameters : PhaseParameters) (mode : ℤ × ℤ) (time : ℝ) : ℝ :=
  collarCutoff1D time * conjugatedExponentialProfile parameters mode time

theorem conjugatedProfile_decay (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (timeBound : time ≤ 1) :
    ‖conjugatedProfile parameters mode time‖ ≤
      Real.exp (-boundaryDecayRate parameters * boundaryFrequency mode * time) := by
  rw [conjugatedProfile, conjugatedExponentialProfile, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (collarCutoff1D_range time).1 (Real.exp_pos _).le)]
  exact (mul_le_of_le_one_left (Real.exp_pos _).le (collarCutoff1D_range time).2).trans
    (conjugatedExponentialProfile_decay parameters mode time timeNonnegative timeBound)

def radialLine (time : ℝ) : SpatialPlane := WithLp.toLp 2 ![1 - time, 0]

theorem radialLine_smooth : ContDiff ℝ ∞ radialLine := by
  rw [contDiff_piLp]
  intro coordinate
  fin_cases coordinate <;> simp [radialLine] <;> fun_prop

theorem radialLine_norm (time : ℝ) : ‖radialLine time‖ = |1 - time| := by
  simpa only [radialLine, collarPlane, Real.cos_zero, Real.sin_zero, mul_one, mul_zero] using
    collarPlane_norm time 0

theorem radialBoundaryPhaseDifference_eq (parameters : PhaseParameters) (cell : ℤ) (time : ℝ) :
    radialBoundaryPhaseDifference parameters cell time =
      cartesianPhase parameters cell (radialLine time) - boundaryPhase parameters cell := by
  rw [cartesianPhase_formula, radialLine_norm]
  unfold radialBoundaryPhaseDifference boundaryPhase
  simp only [sq_abs, mul_pow]
  ring

theorem conjugatedExponentialProfile_weight (parameters : PhaseParameters) (mode : ℤ × ℤ) (time : ℝ) :
    conjugatedExponentialProfile parameters mode time =
      Real.exp (-boundaryFrequency mode * time) *
        (cartesianWeight parameters mode.2 (radialLine time) / Real.exp (boundaryPhase parameters mode.2)) := by
  rw [conjugatedExponentialProfile, radialBoundaryPhaseDifference_eq, cartesianWeight_exp,
    Real.exp_add, Real.exp_sub]

theorem conjugatedProfile_smooth (parameters : PhaseParameters) (mode : ℤ × ℤ) :
    ContDiff ℝ ∞ (conjugatedProfile parameters mode) := by
  have representation : conjugatedProfile parameters mode = fun time =>
      collarCutoff1D time * (Real.exp (-boundaryFrequency mode * time) *
        (cartesianWeight parameters mode.2 (radialLine time) / Real.exp (boundaryPhase parameters mode.2))) := by
    funext time
    rw [conjugatedProfile, conjugatedExponentialProfile_weight]
  rw [representation]
  exact collarCutoff1D_smooth.mul (((contDiff_const.mul contDiff_id).exp).mul
    (((cartesianWeight_contDiff parameters mode.2).comp radialLine_smooth).div_const _))

end Grad.BoundaryLift
