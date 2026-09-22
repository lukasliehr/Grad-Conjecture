import AKDR5OriginalEquivariantAverageNorm
import AKBG3BoundedCovariantPrimitive

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
open Set
open scoped ContDiff
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.CartesianStartup Grad.Constraints
open Grad.NonlinearProduct Grad.NonlinearQuotientBounds Grad.GaugeCoefficients.Physical.RadialLedger

private theorem angle_cosine_bound (angle : ℝ) (inside : angle ∈ Icc (0 : ℝ) (2*Real.pi)) :
    ‖((angle * Real.cos angle : ℝ) : ℂ)‖ ≤ 2*Real.pi := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg inside.1]
  exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one angle) inside.1).trans
    (by simpa only [mul_one] using inside.2)

private theorem angle_sine_bound (angle : ℝ) (inside : angle ∈ Icc (0 : ℝ) (2*Real.pi)) :
    ‖((angle * Real.sin angle : ℝ) : ℂ)‖ ≤ 2*Real.pi := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg inside.1]
  exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one angle) inside.1).trans
    (by simpa only [mul_one] using inside.2)

def originalPrimitiveCosineCore (parameters : PhaseParameters) (field : ACore parameters 2) : ACore parameters 2 :=
  originalAngularKernelCore parameters (fun angle => ((angle*Real.cos angle : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp (contDiff_id.mul Real.contDiff_cos))
    (2*Real.pi) (by positivity) angle_cosine_bound field

def originalPrimitiveSineCore (parameters : PhaseParameters) (field : ACore parameters 2) : ACore parameters 2 :=
  originalAngularKernelCore parameters (fun angle => ((angle*Real.sin angle : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp (contDiff_id.mul Real.contDiff_sin))
    (2*Real.pi) (by positivity) angle_sine_bound field

def originalCovariantPrimitiveCore (parameters : PhaseParameters) (field : ACore parameters 2) : ACore parameters 2 :=
  originalPrimitiveCosineCore parameters field -
    valueMapCore parameters quarterValueMap (originalPrimitiveSineCore parameters field)

def originalCovariantPrimitiveConstant (grade : ℕ) : ℝ :=
  (1+‖quarterValueMap‖)*(2*Real.pi*orthogonalGradeConstant grade)

theorem originalCovariantPrimitiveConstant_nonnegative (grade : ℕ) :
    0 ≤ originalCovariantPrimitiveConstant grade :=
  mul_nonneg (add_nonneg zero_le_one (norm_nonneg _))
    (mul_nonneg (by positivity) (orthogonalGradeConstant_nonnegative _))

theorem originalCovariantPrimitiveCore_bound (parameters : PhaseParameters)
    (field : ACore parameters 2) (grade : ℕ) :
    originalGradeNorm grade (originalCovariantPrimitiveCore parameters field) ≤
      originalCovariantPrimitiveConstant grade * originalGradeNorm grade field := by
  have cosine := originalAngularKernelCore_bound parameters (fun angle => ((angle*Real.cos angle : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp (contDiff_id.mul Real.contDiff_cos))
    (2*Real.pi) (by positivity) angle_cosine_bound field grade
  have sine := originalAngularKernelCore_bound parameters (fun angle => ((angle*Real.sin angle : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp (contDiff_id.mul Real.contDiff_sin))
    (2*Real.pi) (by positivity) angle_sine_bound field grade
  change originalGradeNorm grade (originalPrimitiveCosineCore parameters field) ≤ _ at cosine
  change originalGradeNorm grade (originalPrimitiveSineCore parameters field) ≤ _ at sine
  have mapped := (valueMapCore_bound quarterValueMap _ grade).trans
    (mul_le_mul_of_nonneg_left sine (norm_nonneg _))
  exact (originalGradeNorm_sub_le grade _ _).trans
    ((add_le_add cosine mapped).trans_eq (by unfold originalCovariantPrimitiveConstant; ring))

theorem originalCovariantPrimitiveCore_sameField (parameters : PhaseParameters)
    (field : ACore parameters 2) :
    originalSourceFieldLinear parameters (originalCovariantPrimitiveCore parameters field) =
      startupCovariantPrimitiveKernel (originalSourceFieldLinear parameters field) := by
  rw [originalCovariantPrimitiveCore,map_sub,originalSourceFieldLinear_valueMap]
  have cosine := originalAngularKernelCore_sameField parameters (fun angle => ((angle*Real.cos angle : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp (contDiff_id.mul Real.contDiff_cos))
    (2*Real.pi) (by positivity) angle_cosine_bound field
  have sine := originalAngularKernelCore_sameField parameters (fun angle => ((angle*Real.sin angle : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp (contDiff_id.mul Real.contDiff_sin))
    (2*Real.pi) (by positivity) angle_sine_bound field
  change originalSourceFieldLinear parameters (originalPrimitiveCosineCore parameters field) = _ at cosine
  change originalSourceFieldLinear parameters (originalPrimitiveSineCore parameters field) = _ at sine
  rw [cosine,sine]
  rfl

end Grad.OriginalCoreRealization
