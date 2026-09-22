import ANR17PolarLaplacian

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.NonlinearQuotient Grad.PhysicalFamily

def polarTestModel (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (point : ℝ × ℝ) : ComplexEuclidean 1 :=
  test point.1 • (cellExponential mode point.2 • vector)

theorem polarTestModel_smooth (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ test) : ContDiff ℝ ∞ (polarTestModel mode vector test) :=
  (smooth.comp contDiff_fst).smul (((cellExponential_smooth mode).comp contDiff_snd).smul contDiff_const)

theorem radialTestLift_model (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (radius : ℝ) (positive : 0 < radius) (angle : ℝ) :
    radialTestLift mode vector test (polarPlane (radius, angle)) = polarTestModel mode vector test (radius, angle) := by
  rw [radialTestLift_polar mode vector test radius positive angle,
    show fourier mode (angle : CellCircle) = cellExponential mode angle from cellCharacter_coe _ _,
    mul_smul, Complex.coe_smul]
  rfl

theorem polarTestModel_radial (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ test) :
    radialField (polarTestModel mode vector test) = polarTestModel mode vector (deriv test) := by
  funext point
  exact (radialField_hasDerivAt _ (polarTestModel_smooth mode vector test smooth) point.1 point.2).unique
    (((smooth.differentiable (by simp)) point.1).hasDerivAt.smul_const (cellExponential mode point.2 • vector))

theorem polarTestModel_radial_two (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ test) :
    radialIter 2 (polarTestModel mode vector test) = polarTestModel mode vector (deriv (deriv test)) := by
  have two : radialIter 2 (polarTestModel mode vector test) = radialField (radialField (polarTestModel mode vector test)) := rfl
  exact two.trans ((congrArg radialField (polarTestModel_radial mode vector test smooth)).trans
    (polarTestModel_radial mode vector (deriv test) (contDiff_infty_iff_deriv.mp smooth).2))

private theorem cellExponential_derivative (mode : ℤ) (angle : ℝ) :
    HasDerivAt (cellExponential mode) ((Complex.I * (mode : ℂ)) * cellExponential mode angle) angle := by
  have derivative := (cellExponential_hasFDerivAt mode angle).hasDerivAt
  have slope : cellExponentialDerivative mode angle 1 =
      (Complex.I * (mode : ℂ)) * cellExponential mode angle := by
    change ((Complex.I * (mode : ℂ)) * (1 : ℂ)) * cellExponential mode angle = _
    rw [mul_one]
  exact derivative.congr_deriv slope

private theorem polarTestModel_angle (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (radius angle : ℝ) :
    HasDerivAt (fun current => polarTestModel mode vector test (radius, current))
      (polarTestModel mode ((Complex.I * (mode : ℂ)) • vector) test (radius, angle)) angle := by
  have derivative := ((cellExponential_derivative mode angle).smul_const vector).const_smul (test radius)
  have slope : test radius • (((Complex.I * (mode : ℂ)) * cellExponential mode angle) • vector) =
      polarTestModel mode ((Complex.I * (mode : ℂ)) • vector) test (radius, angle) := by
    change test radius • (((Complex.I * (mode : ℂ)) * cellExponential mode angle) • vector) =
      test radius • (cellExponential mode angle • ((Complex.I * (mode : ℂ)) • vector))
    rw [mul_smul]
    exact congrArg (fun value : ComplexEuclidean 1 => test radius • value)
      (smul_comm (Complex.I * (mode : ℂ)) (cellExponential mode angle) vector)
  exact derivative.congr_deriv slope

theorem polarTestModel_angular (order : ℕ) (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ test) :
    angularJet order (polarTestModel mode vector test) =
      polarTestModel mode ((Complex.I * (mode : ℂ)) ^ order • vector) test := by
  induction order with
  | zero => simp only [angularJet_zero, pow_zero, one_smul]
  | succ order previous =>
    funext point
    have first := angularJet_hasDerivAt order (polarTestModel mode vector test)
      (polarTestModel_smooth mode vector test smooth) point.1 point.2
    have expression : (fun angle => angularJet order (polarTestModel mode vector test) (point.1, angle)) =
        (fun angle => polarTestModel mode ((Complex.I * (mode : ℂ)) ^ order • vector) test (point.1, angle)) := by
      funext angle
      exact congrFun previous (point.1, angle)
    rw [expression] at first
    have result := first.unique (polarTestModel_angle mode ((Complex.I * (mode : ℂ)) ^ order • vector) test point.1 point.2)
    simpa only [smul_smul, ← pow_succ'] using result

end Grad.CircularHighRegularity
