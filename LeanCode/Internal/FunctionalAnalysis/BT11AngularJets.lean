import BT10AngularDerivative

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace Grad.BoundaryTrace

open Grad.ClosedJets Grad.CartesianState

def angularJet {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (order : ℕ) (field : ℝ × ℝ → Value) (point : ℝ × ℝ) : Value :=
  iteratedFDeriv ℝ order field point (fun _ => (0, 1))

theorem angularJet_zero {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : ℝ × ℝ → Value) : angularJet 0 field = field := by
  funext point
  simp only [angularJet, iteratedFDeriv_zero_apply]

theorem angularJet_smooth {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (order : ℕ) (field : ℝ × ℝ → Value) (smooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (angularJet order field) := by
  let evaluation := ContinuousMultilinearMap.apply ℝ (fun _ : Fin order => ℝ × ℝ) Value
    (fun _ => (0, 1))
  exact evaluation.contDiff.comp (smooth.iteratedFDeriv_right (m := ∞) (i := order) (by norm_cast))

theorem angularJet_hasDerivAt {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (order : ℕ) (field : ℝ × ℝ → Value) (smooth : ContDiff ℝ ∞ field) (time angle : ℝ) :
    HasDerivAt (fun angular : ℝ => angularJet order field (time, angular))
      (angularJet (order + 1) field (time, angle)) angle := by
  have insertion : HasDerivAt (fun angular : ℝ => (time, angular)) (0, 1) angle :=
    (hasDerivAt_const angle time).prodMk (hasDerivAt_id angle)
  have derivative := ((angularJet_smooth order field smooth).differentiable (by simp)
    (time, angle)).hasFDerivAt.comp_hasDerivAt angle insertion
  apply derivative.congr_deriv
  symm
  exact ((smooth.contDiffAt.iteratedFDeriv_right (m := ∞) (i := order) (by norm_cast)).differentiableAt
    (by simp)).iteratedFDeriv_succ_apply_left' (m := fun _ => (0, 1))

theorem angularJet_norm_le {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (order : ℕ) (field : ℝ × ℝ → Value) (point : ℝ × ℝ) :
    ‖angularJet order field point‖ ≤ ‖iteratedFDeriv ℝ order field point‖ := by
  have bound := (iteratedFDeriv ℝ order field point).le_opNorm (fun _ => ((0, 1) : ℝ × ℝ))
  simpa only [angularJet, Prod.norm_def, norm_zero, norm_one, max_eq_right zero_le_one,
    Finset.prod_const_one, mul_one] using bound

theorem periodic_iteratedFDeriv {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (order : ℕ) (field : ℝ × ℝ → Value)
    (periodic : Function.Periodic field (0, 2 * Real.pi)) :
    Function.Periodic (iteratedFDeriv ℝ order field) (0, 2 * Real.pi) := by
  intro point
  have equality : (fun input : ℝ × ℝ => field (input + (0, 2 * Real.pi))) = field := funext periodic
  rw [← iteratedFDeriv_comp_add_right order (0, 2 * Real.pi) point, equality]

theorem angularJet_endpoint {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (order : ℕ) (field : ℝ × ℝ → Value)
    (periodic : Function.Periodic field (0, 2 * Real.pi)) (time : ℝ) :
    angularJet order field (time, Real.pi) = angularJet order field (time, -Real.pi) := by
  have equality := congrArg (fun tensor => tensor (fun _ => ((0, 1) : ℝ × ℝ)))
    (periodic_iteratedFDeriv order field periodic (time, -Real.pi))
  simpa only [angularJet, Prod.mk_add_mk, add_zero, show -Real.pi + 2 * Real.pi = Real.pi by ring] using equality

theorem angularCoefficient_angularJet {dimension : ℕ} (order : ℕ)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (periodic : Function.Periodic field (0, 2 * Real.pi)) (time : ℝ) (mode : ℤ) :
    angularCoefficient (fun angle => angularJet order field (time, angle)) mode =
      (Complex.I * (mode : ℂ)) ^ order • angularCoefficient (fun angle => field (time, angle)) mode := by
  induction order with
  | zero => simp only [angularJet_zero, pow_zero, one_smul]
  | succ order inductionHypothesis =>
    rw [angularCoefficient_derivative (fun angle => angularJet order field (time, angle))
      (fun angle => angularJet (order + 1) field (time, angle))
      ((angularJet_smooth order field smooth).continuous.comp (continuous_const.prodMk continuous_id))
      ((angularJet_smooth (order + 1) field smooth).continuous.comp (continuous_const.prodMk continuous_id))
      (angularJet_hasDerivAt order field smooth time) (angularJet_endpoint order field periodic time),
      inductionHypothesis, smul_smul, pow_succ']

theorem angularJet_bessel_finite {dimension : ℕ} (order : ℕ)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (periodic : Function.Periodic field (0, 2 * Real.pi)) (time : ℝ) (modes : Finset ℤ) :
    (∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * order) * ‖angularCoefficient (fun angle => field (time, angle)) mode‖ ^ 2) ≤
      (2 * Real.pi)⁻¹ * ∫ angle in -Real.pi..Real.pi, ‖angularJet order field (time, angle)‖ ^ 2 := by
  have bessel := angular_bessel_finite (fun angle => angularJet order field (time, angle))
    ((angularJet_smooth order field smooth).continuous.comp (continuous_const.prodMk continuous_id)) modes
  apply le_trans _ bessel
  apply Finset.sum_le_sum
  intro mode _
  rw [angularCoefficient_angularJet order field smooth periodic time mode, norm_smul, norm_pow, norm_mul,
    Complex.norm_I, one_mul]
  have normCast : ‖(mode : ℂ)‖ = |(mode : ℝ)| := by norm_cast
  rw [normCast]
  ring_nf
  rfl

end Grad.BoundaryTrace
