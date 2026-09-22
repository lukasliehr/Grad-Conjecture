import ANG16OrthogonalModeSeries

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
namespace Grad.CircularHighWeak
open Grad.CartesianState

theorem firstAngularSeries_summable (parameter : ℝ) (source : highDiskL2) :
    Summable (fun mode : ℤ => (Complex.I * (mode : ℂ)) • highDiskMode mode (highRobinWeakInverse parameter source)) :=
  highModeSeries_summable _ _ (2 * ‖source‖) (by positivity) (fun modes =>
    (congrArg norm (highFiniteRotation_apply modes (highRobinWeakInverse parameter source))).symm.le.trans
      (highRobinWeakInverse_first_bound parameter modes source))

/-- The genuine first angular derivative belongs to the full high H1
completion, constructed by the convergent orthogonal mode series. -/
def firstAngularWeakSolution (parameter : ℝ) (source : highDiskL2) : highDiskGrade :=
  ∑' mode : ℤ, (Complex.I * (mode : ℂ)) • highDiskMode mode (highRobinWeakInverse parameter source)

theorem firstAngularWeakSolution_bound (parameter : ℝ) (source : highDiskL2) :
    ‖firstAngularWeakSolution parameter source‖ ≤ 2 * ‖source‖ :=
  highModeSeries_bound _ _ (2 * ‖source‖) (by positivity) (fun modes =>
    (congrArg norm (highFiniteRotation_apply modes (highRobinWeakInverse parameter source))).symm.le.trans
      (highRobinWeakInverse_first_bound parameter modes source))

theorem firstAngularWeakSolution_mode (parameter : ℝ) (source : highDiskL2) (mode : ℤ) :
    highDiskMode mode (firstAngularWeakSolution parameter source) =
      (Complex.I * (mode : ℂ)) • highDiskMode mode (highRobinWeakInverse parameter source) := by
  have mapped := (highDiskMode mode).map_tsum (firstAngularSeries_summable parameter source)
  have sumEquality : (∑' other : ℤ, highDiskMode mode ((Complex.I * (other : ℂ)) •
      highDiskMode other (highRobinWeakInverse parameter source))) =
      highDiskMode mode ((Complex.I * (mode : ℂ)) • highDiskMode mode (highRobinWeakInverse parameter source)) := by
    apply tsum_eq_single mode
    intro other different
    exact ((highDiskMode mode).map_smul (Complex.I * (other : ℂ))
      (highDiskMode other (highRobinWeakInverse parameter source))).trans
      ((congrArg (fun value : highDiskGrade => (Complex.I * (other : ℂ)) • value)
        ((highDiskMode_projection mode other (highRobinWeakInverse parameter source)).trans (if_neg (Ne.symm different)))).trans
        (smul_zero _))
  exact mapped.trans (sumEquality.trans
    (((highDiskMode mode).map_smul (Complex.I * (mode : ℂ))
      (highDiskMode mode (highRobinWeakInverse parameter source))).trans
      (congrArg (fun value : highDiskGrade => (Complex.I * (mode : ℂ)) • value)
        ((highDiskMode_projection mode mode (highRobinWeakInverse parameter source)).trans (if_pos rfl)))))

/-- The H1 series represents precisely the already identified weak Cartesian
rotation of the constructed weak solution; it introduces no regularity hypothesis. -/
theorem firstAngularWeakSolution_bulk (parameter : ℝ) (source : highDiskL2) :
    highDiskBulk (firstAngularWeakSolution parameter source) =
      highRotation (highRobinWeakInverse parameter source) := by
  apply diskFourierIsometry.injective
  apply lp.ext
  funext mode
  change diskMode mode (highDiskBulk (firstAngularWeakSolution parameter source)) =
    diskMode mode (highRotation (highRobinWeakInverse parameter source))
  have projected := (highDiskMode_bulk mode (firstAngularWeakSolution parameter source)).symm.trans
    ((congrArg highDiskBulk (firstAngularWeakSolution_mode parameter source mode)).trans
      (highDiskBulk.map_smul (Complex.I * (mode : ℂ)) (highDiskMode mode (highRobinWeakInverse parameter source))))
  exact projected.trans
    ((congrArg (fun value : DiskL2 1 => (Complex.I * (mode : ℂ)) • value)
      (highDiskMode_bulk mode (highRobinWeakInverse parameter source))).trans
      (highRotation_coefficient mode (highRobinWeakInverse parameter source)).symm)

end Grad.CircularHighWeak
