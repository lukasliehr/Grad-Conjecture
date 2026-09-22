import AKAQ3SameGradeFourierPayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped BigOperators
namespace Grad.OriginalFlatAxisDecay
open Grad.FourierGrade Grad.CartesianState Grad.ClosedJets

def waveAngle (mode : SpatialMode) (point : SpatialPlane) : ℝ :=
  (Real.pi / 2) * ((mode.1 : ℝ) * point 0 + (mode.2 : ℝ) * point 1)

def rotationWave (mode : SpatialMode) (point : SpatialPlane) : ℝ :=
  (Real.pi / 2) * (-(mode.1 : ℝ) * point 1 + (mode.2 : ℝ) * point 0)

theorem spatialMode_sum_abs (mode : SpatialMode) :
    |(mode.1 : ℝ)| + |(mode.2 : ℝ)| ≤ 2 * Real.sqrt (spatialSquare mode) := by
  have square := Real.sq_sqrt (spatialSquare_positive mode).le
  have nonnegative := Real.sqrt_nonneg (spatialSquare mode)
  change Real.sqrt (spatialSquare mode)^2 = 1 + (mode.1 : ℝ)^2 + (mode.2 : ℝ)^2 at square
  nlinarith [sq_abs (mode.1 : ℝ),sq_abs (mode.2 : ℝ),sq_nonneg (|(mode.1 : ℝ)| - |(mode.2 : ℝ)|)]

theorem linearAngle_abs (mode : SpatialMode) (first second : ℝ) (radius : ℝ)
    (firstBound : |first| ≤ radius) (secondBound : |second| ≤ radius) :
    |(Real.pi / 2) * ((mode.1 : ℝ) * first + (mode.2 : ℝ) * second)| ≤
      Real.pi * Real.sqrt (spatialSquare mode) * radius := by
  have radiusNonnegative : 0 ≤ radius := (abs_nonneg first).trans firstBound
  rw [abs_mul,abs_of_pos (by positivity : 0 < Real.pi / 2)]
  calc
    _ ≤ (Real.pi / 2) * (|(mode.1 : ℝ)| * |first| + |(mode.2 : ℝ)| * |second|) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [abs_mul] using abs_add_le ((mode.1 : ℝ) * first) ((mode.2 : ℝ) * second)
    _ ≤ (Real.pi / 2) * ((|(mode.1 : ℝ)| + |(mode.2 : ℝ)|) * radius) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left firstBound (abs_nonneg (mode.1 : ℝ)),mul_le_mul_of_nonneg_left secondBound (abs_nonneg (mode.2 : ℝ))]
    _ ≤ (Real.pi / 2) * ((2 * Real.sqrt (spatialSquare mode)) * radius) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (spatialMode_sum_abs mode) radiusNonnegative) (by positivity)
    _ = _ := by ring

theorem waveAngle_abs (mode : SpatialMode) (point : SpatialPlane) :
    |waveAngle mode point| ≤ Real.pi * Real.sqrt (spatialSquare mode) * ‖point‖ :=
  linearAngle_abs mode _ _ _ (spatialCoordinate_abs_le_norm point 0) (spatialCoordinate_abs_le_norm point 1)

theorem rotationWave_abs (mode : SpatialMode) (point : SpatialPlane) :
    |rotationWave mode point| ≤ Real.pi * Real.sqrt (spatialSquare mode) * ‖point‖ := by
  have bound := linearAngle_abs mode (-point 1) (point 0) ‖point‖
    (by simpa using spatialCoordinate_abs_le_norm point 1) (spatialCoordinate_abs_le_norm point 0)
  simpa only [rotationWave,neg_mul,mul_neg] using bound

def taylorSymbol (point : SpatialPlane) (mode : SpatialMode) : ℂ :=
  Complex.exp (Complex.I * (waveAngle mode point : ℂ)) - 1 - Complex.I * (waveAngle mode point : ℂ)

def rotationRemainderSymbol (point : SpatialPlane) (mode : SpatialMode) : ℂ :=
  (Complex.I * (rotationWave mode point : ℂ)) *
    (Complex.exp (Complex.I * (waveAngle mode point : ℂ)) - 1)

theorem taylorSymbol_bound (point : SpatialPlane) (mode : SpatialMode) :
    ‖taylorSymbol point mode‖^2 ≤ (9 * Real.pi^3 * ‖point‖^3) * Real.sqrt (spatialSquare mode)^3 := by
  have cubed := pow_le_pow_left₀ (abs_nonneg (waveAngle mode point)) (waveAngle_abs mode point) 3
  have bound := imaginary_exp_taylor_sq (waveAngle mode point)
  unfold taylorSymbol
  nlinarith only [bound,cubed]

theorem rotationRemainderSymbol_bound (point : SpatialPlane) (mode : SpatialMode) :
    ‖rotationRemainderSymbol point mode‖^2 ≤ (4 * Real.pi^3 * ‖point‖^3) * Real.sqrt (spatialSquare mode)^3 := by
  have frequency := pow_le_pow_left₀ (abs_nonneg (rotationWave mode point)) (rotationWave_abs mode point) 2
  have difference := (imaginary_exp_difference_sq (waveAngle mode point)).trans
    (mul_le_mul_of_nonneg_left (waveAngle_abs mode point) (by norm_num : 0 ≤ (4:ℝ)))
  have product := mul_le_mul frequency difference (sq_nonneg _) (by positivity : 0 ≤ (Real.pi * Real.sqrt (spatialSquare mode) * ‖point‖)^2)
  simp only [rotationRemainderSymbol,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
  nlinarith only [product]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem finiteFourier_taylor_bound (point : SpatialPlane) (field : JGrade E 4)
    (cells : Finset ℤ) (support : Finset SpatialMode) :
    ∑ cell ∈ cells, cellFrequency cell^2 *
      ‖∑ mode ∈ support, taylorSymbol point mode • coefficient 4 field (fibreMode (cell,mode))‖^2 ≤
      9 * Real.pi^3 * ‖point‖^3 * spatialDecayConstant * ‖field‖^2 :=
  finiteFourier_symbol_bound _ _ (by positivity) (taylorSymbol_bound point) field cells support

theorem finiteFourier_rotationRemainder_bound (point : SpatialPlane) (field : JGrade E 4)
    (cells : Finset ℤ) (support : Finset SpatialMode) :
    ∑ cell ∈ cells, cellFrequency cell^2 *
      ‖∑ mode ∈ support, rotationRemainderSymbol point mode • coefficient 4 field (fibreMode (cell,mode))‖^2 ≤
      4 * Real.pi^3 * ‖point‖^3 * spatialDecayConstant * ‖field‖^2 :=
  finiteFourier_symbol_bound _ _ (by positivity) (rotationRemainderSymbol_bound point) field cells support

end Grad.OriginalFlatAxisDecay
