import ANR19TestLaplacian

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.NonlinearQuotient

/-- The literal radial Laplacian on a character test. Compact support away
from zero removes the apparent singularity, including for both derivatives. -/
def radialTestOperator (mode : ℤ) (test : ℝ → ℝ) (radius : ℝ) : ℝ :=
  deriv (deriv test) radius + radius⁻¹ * deriv test radius -
    (mode : ℝ) ^ 2 * (radius⁻¹) ^ 2 * test radius

theorem radialTestOperator_support (mode : ℤ) (test : ℝ → ℝ) :
    tsupport (radialTestOperator mode test) ⊆ tsupport test := by
  have firstSupport : tsupport (deriv test) ⊆ tsupport test := tsupport_deriv_subset
  have secondSupport : tsupport (deriv (deriv test)) ⊆ tsupport test := tsupport_deriv_subset.trans firstSupport
  apply closure_minimal
  · intro radius member
    by_contra outside
    have valueZero := image_eq_zero_of_notMem_tsupport (f := test) outside
    have firstZero := image_eq_zero_of_notMem_tsupport (f := deriv test) (fun member => outside (firstSupport member))
    have secondZero := image_eq_zero_of_notMem_tsupport (f := deriv (deriv test)) (fun member => outside (secondSupport member))
    exact member (by simp only [radialTestOperator, valueZero, firstZero, secondZero, mul_zero, add_zero, sub_zero])
  · exact isClosed_tsupport _

theorem radialTestOperator_smooth (mode : ℤ) (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test)
    (inside : tsupport test ⊆ Ioo (0 : ℝ) 1) : ContDiff ℝ ∞ (radialTestOperator mode test) := by
  have firstSmooth := (contDiff_infty_iff_deriv.mp smooth).2
  have secondSmooth := (contDiff_infty_iff_deriv.mp firstSmooth).2
  rw [contDiff_iff_contDiffAt]
  intro radius
  by_cases zero : radius = 0
  · subst radius
    have outside : (0 : ℝ) ∉ tsupport (radialTestOperator mode test) :=
      fun member => (inside (radialTestOperator_support mode test member)).1.false
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport (radialTestOperator mode test)).isOpen_compl.mem_nhds outside] with radius absent
    exact image_eq_zero_of_notMem_tsupport absent
  · have inverse : ContDiffAt ℝ ∞ (fun radius : ℝ => radius⁻¹) radius := contDiffAt_id.fun_inv zero
    exact (secondSmooth.contDiffAt.add (inverse.mul firstSmooth.contDiffAt)).sub
      ((contDiffAt_const.mul (inverse.pow 2)).mul smooth.contDiffAt)

/-- Actual Cartesian test Laplacian, with literal reciprocal-radius terms,
proved from the multiplied polar identity and positive-radius cancellation. -/
theorem radialTestLift_laplacian_polar (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ test) (supported : tsupport test ⊆ Ioo (0 : ℝ) 1)
    (radius angle : ℝ) (inside : radius ∈ Ioo (0 : ℝ) 1) :
    diskLaplacian (radialTestLift mode vector test) (polarPlane (radius, angle)) =
      radialTestLift mode vector (radialTestOperator mode test) (polarPlane (radius, angle)) := by
  apply smul_right_injective (ComplexEuclidean 1) (pow_ne_zero 2 inside.1.ne')
  dsimp only
  rw [radialTestLift_laplacian_multiplied mode vector test smooth supported radius angle inside,
    radialTestLift_model mode vector (radialTestOperator mode test) radius inside.1 angle]
  change _ = radius ^ 2 • (radialTestOperator mode test radius • (cellExponential mode angle • vector))
  rw [smul_smul]
  apply congrArg (fun scalar : ℝ => scalar • (cellExponential mode angle • vector))
  unfold radialTestOperator
  field_simp [inside.1.ne']

end Grad.CircularHighRegularity
