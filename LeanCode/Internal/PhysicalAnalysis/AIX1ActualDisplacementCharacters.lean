import AIQ15UniformPhysicalHighInverseConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularKernelOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction

abbrev OrbitParameter := ℝ × ℝ

def orbitAngle (tau : OrbitParameter) (mode : ℤ × ℤ) : ℝ :=
  (mode.1 : ℝ) * tau.1 + (mode.2 : ℝ) * tau.2

def orbitCharacter (tau : OrbitParameter) (mode : ℤ × ℤ) : ℂ :=
  Complex.exp (Complex.I * (orbitAngle tau mode : ℂ))

theorem orbitCharacter_norm (tau : OrbitParameter) (mode : ℤ × ℤ) :
    ‖orbitCharacter tau mode‖ = 1 := Complex.norm_exp_I_mul_ofReal _

theorem orbitCharacter_add (tau sigma : OrbitParameter) (mode : ℤ × ℤ) :
    orbitCharacter (tau + sigma) mode = orbitCharacter tau mode * orbitCharacter sigma mode := by
  unfold orbitCharacter orbitAngle
  rw [← Complex.exp_add]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast
  ring

theorem orbitCharacter_mode_add (tau : OrbitParameter) (first second : ℤ × ℤ) :
    orbitCharacter tau (first + second) = orbitCharacter tau first * orbitCharacter tau second := by
  unfold orbitCharacter orbitAngle
  rw [← Complex.exp_add]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast
  ring

@[simp] theorem orbitCharacter_zero (mode : ℤ × ℤ) : orbitCharacter 0 mode = 1 := by
  simp [orbitCharacter, orbitAngle]

theorem orbitCharacter_inverse (tau : OrbitParameter) (mode : ℤ × ℤ) :
    orbitCharacter tau mode * orbitCharacter (-tau) mode = 1 := by
  rw [← orbitCharacter_add, add_neg_cancel, orbitCharacter_zero]

theorem orbitCharacter_displacement (tau : OrbitParameter) (shift mode : ℤ × ℤ) :
    orbitCharacter tau mode * orbitCharacter (-tau) (twoFrequencyTranslation shift mode) =
      orbitCharacter tau shift := by
  have decomposition : mode = shift + twoFrequencyTranslation shift mode := by
    ext <;> simp [twoFrequencyTranslation_apply]
  calc
    _ = (orbitCharacter tau shift * orbitCharacter tau (twoFrequencyTranslation shift mode)) *
        orbitCharacter (-tau) (twoFrequencyTranslation shift mode) := by
      conv_lhs => arg 1; rw [decomposition, orbitCharacter_mode_add]
    _ = _ := by rw [mul_assoc, orbitCharacter_inverse, mul_one]

def orbitStepSize (step : OrbitParameter) : ℝ := |step.1| + |step.2|

theorem orbitAngle_bound (step : OrbitParameter) (shift : ℤ × ℤ) :
    |orbitAngle step shift| ≤ annularFrequency shift.1 shift.2 * orbitStepSize step := by
  unfold orbitAngle orbitStepSize annularFrequency
  have first := abs_add_le ((shift.1 : ℝ) * step.1) ((shift.2 : ℝ) * step.2)
  rw [abs_mul, abs_mul] at first
  nlinarith [abs_nonneg step.1, abs_nonneg step.2,
    abs_nonneg (shift.1 : ℝ), abs_nonneg (shift.2 : ℝ),
    mul_nonneg (abs_nonneg (shift.1 : ℝ)) (abs_nonneg step.2),
    mul_nonneg (abs_nonneg (shift.2 : ℝ)) (abs_nonneg step.1)]

theorem imaginaryExp_increment_bound (angle : ℝ) :
    ‖Complex.exp (Complex.I * (angle : ℂ)) - 1‖ ≤ 2 * |angle| := by
  have normArg : ‖Complex.I * (angle : ℂ)‖ = |angle| := by simp
  by_cases small : |angle| ≤ 1
  · simpa only [normArg] using Complex.norm_exp_sub_one_le (normArg.trans_le small)
  · have rough : ‖Complex.exp (Complex.I * (angle : ℂ)) - 1‖ ≤ 2 := by
      simpa only [Complex.norm_exp_I_mul_ofReal, norm_one, one_add_one_eq_two] using
        norm_sub_le (Complex.exp (Complex.I * (angle : ℂ))) 1
    exact rough.trans (by linarith)

theorem imaginaryExp_remainder_bound (angle : ℝ) :
    ‖Complex.exp (Complex.I * (angle : ℂ)) - 1 - Complex.I * (angle : ℂ)‖ ≤ 3 * |angle| ^ 2 := by
  have normArg : ‖Complex.I * (angle : ℂ)‖ = |angle| := by simp
  by_cases small : |angle| ≤ 1
  · have estimate := Complex.norm_exp_sub_one_sub_id_le (normArg.trans_le small)
    rw [normArg] at estimate
    nlinarith [sq_nonneg |angle|]
  · have rough : ‖Complex.exp (Complex.I * (angle : ℂ)) - 1 - Complex.I * (angle : ℂ)‖ ≤ 2 + |angle| := by
      calc
        _ ≤ ‖Complex.exp (Complex.I * (angle : ℂ)) - 1‖ + ‖Complex.I * (angle : ℂ)‖ := norm_sub_le _ _
        _ ≤ (‖Complex.exp (Complex.I * (angle : ℂ))‖ + ‖(1 : ℂ)‖) + |angle| :=
          add_le_add (norm_sub_le _ _) normArg.le
        _ = _ := by rw [Complex.norm_exp_I_mul_ofReal, norm_one]; norm_num
    exact rough.trans (by nlinarith [abs_nonneg angle])

end Grad.AnnularKernelOrbit
