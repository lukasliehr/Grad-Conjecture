import AKAC30SameActualPhysicalRecoveryConsumer
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter
open scoped Topology ContDiff
namespace Grad.ActualCartesianDescent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance descentAngularPeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem periodic_value_of_angle_eq (field : ℝ → E) (periodic : Function.Periodic field (2*Real.pi))
    {first second : ℝ} (same : (first : Real.Angle) = (second : Real.Angle)) : field first = field second :=
  congrArg periodic.lift same

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem periodic_arg_negative (field : ℝ → E) (periodic : Function.Periodic field (2*Real.pi))
    (point : ℂ) (nonzero : point ≠ 0) :
    field (Complex.arg (-point)+Real.pi) = field (Complex.arg point) := by
  apply periodic_value_of_angle_eq field periodic
  rw [Real.Angle.coe_add,Complex.arg_neg_coe_angle nonzero]
  rw [add_assoc,← Real.Angle.coe_add,show Real.pi+Real.pi=2*Real.pi by ring,Real.Angle.coe_two_pi,add_zero]

theorem complexArgument_smoothAt (point : ℂ) (inside : point ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ Complex.arg point := by
  have smooth : ContDiffAt ℝ ∞ Complex.log point := (Complex.contDiffAt_log inside).restrict_scalars ℝ
  simpa only [Function.comp_def,Complex.imCLM_apply,Complex.log_im] using Complex.imCLM.contDiff.contDiffAt.comp point smooth

/-- A periodic polar field gives a definite Cartesian field using arg. The
subsequent theorem proves smoothness across the arg branch cut as well. -/
def cartesianFromPolar (field : ℝ × (ℝ × ℝ) → E) (point : ℂ × ℝ) : E :=
  field (‖point.1‖,Complex.arg point.1,point.2)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem cartesianFromPolar_at_polar (field : ℝ × (ℝ × ℝ) → E)
    (periodic : ∀ radius axial,Function.Periodic (fun polar => field (radius,polar,axial)) (2*Real.pi))
    (radius : ℝ) (positive : 0 < radius) (polar axial : ℝ) :
    cartesianFromPolar field ((radius : ℂ)*(Real.cos polar+Real.sin polar*Complex.I),axial) =
      field (radius,polar,axial) := by
  unfold cartesianFromPolar
  have norm : ‖(radius : ℂ)*(Real.cos polar+Real.sin polar*Complex.I)‖ = radius := by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg positive.le]
    have unit : ‖(Real.cos polar : ℂ)+(Real.sin polar : ℂ)*Complex.I‖ = 1 := by
      rw [Complex.ofReal_cos,Complex.ofReal_sin,← Complex.exp_mul_I]
      exact Complex.norm_exp_ofReal_mul_I polar
    rw [unit,mul_one]
  rw [norm]
  apply periodic_value_of_angle_eq _ (periodic radius axial)
  have same := Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod positive polar
  simp only [Complex.ofReal_cos,Complex.ofReal_sin]
  rw [same]
  simp

/-- The two smooth logarithm charts cover every nonzero point. Periodicity
proves their equality, so no branch-cut smoothness hypothesis is assumed. -/
theorem cartesianFromPolar_smoothAt (field : ℝ × (ℝ × ℝ) → E)
    (lower upper : ℝ)
    (smooth : ContDiffOn ℝ ∞ field (Ioo lower upper ×ˢ (univ : Set (ℝ × ℝ))))
    (periodic : ∀ radius axial,Function.Periodic (fun polar => field (radius,polar,axial)) (2*Real.pi))
    (point : ℂ × ℝ) (nonzero : point.1 ≠ 0) (inside : ‖point.1‖ ∈ Ioo lower upper) :
    ContDiffAt ℝ ∞ (cartesianFromPolar field) point := by
  have normSmooth : ContDiffAt ℝ ∞ (fun source : ℂ × ℝ => ‖source.1‖) point :=
    (contDiffAt_norm ℝ nonzero).comp point contDiffAt_fst
  have atField (angle : ℝ) : ContDiffAt ℝ ∞ field (‖point.1‖,angle,point.2) :=
    smooth.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨inside,mem_univ _⟩)
  by_cases slit : point.1 ∈ Complex.slitPlane
  · exact (atField (Complex.arg point.1)).comp point
      (normSmooth.prodMk (((complexArgument_smoothAt point.1 slit).comp point contDiffAt_fst).prodMk contDiffAt_snd))
  · have negativeSlit : -point.1 ∈ Complex.slitPlane := by
      change ¬(0 < point.1.re ∨ point.1.im ≠ 0) at slit
      change 0 < (-point.1).re ∨ (-point.1).im ≠ 0
      have imaginary : point.1.im = 0 := (not_or.mp slit).2 |> not_not.mp
      have realNonzero : point.1.re ≠ 0 := by
        intro realZero
        apply nonzero
        exact Complex.ext realZero imaginary
      left
      simpa only [Complex.neg_re] using neg_pos.mpr
        (lt_of_le_of_ne (le_of_not_gt (not_or.mp slit).1) realNonzero)
    have angleSmooth : ContDiffAt ℝ ∞ (fun source : ℂ × ℝ => Complex.arg (-source.1)+Real.pi) point :=
      ((complexArgument_smoothAt (-point.1) negativeSlit).comp point contDiffAt_fst.neg).add contDiffAt_const
    have localSmooth : ContDiffAt ℝ ∞
        (fun source : ℂ × ℝ => field (‖source.1‖,Complex.arg (-source.1)+Real.pi,source.2)) point :=
      (atField (Complex.arg (-point.1)+Real.pi)).comp point (normSmooth.prodMk (angleSmooth.prodMk contDiffAt_snd))
    apply localSmooth.congr_of_eventuallyEq
    filter_upwards [(isOpen_ne_fun continuous_fst continuous_const).mem_nhds nonzero] with source nonzeroSource
    exact (periodic_arg_negative (fun angle => field (‖source.1‖,angle,source.2))
      (periodic ‖source.1‖ source.2) source.1 nonzeroSource).symm

end Grad.ActualCartesianDescent
