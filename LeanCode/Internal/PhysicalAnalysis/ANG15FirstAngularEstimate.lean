import ANG14FiniteRotation

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.CircularHighWeak
open Grad.CartesianState

/-- The actual first commuted source functional uses a derivative of the
test only; its bound is independent of the finite angular cutoff. -/
theorem highRobinWeakInverse_first_functional (parameter : ℝ) (modes : Finset ℤ)
    (source : highDiskL2) (test : highDiskGrade) :
    robinValue parameter (highFiniteRotation modes (highRobinWeakInverse parameter source)) test =
      -inner ℂ (highDiskBulk (highFiniteRotation modes test)) source.val :=
  (robinValue_finiteRotation parameter modes (highRobinWeakInverse parameter source) test).trans
    (congrArg Neg.neg (highRobinWeakInverse_equation parameter source (highFiniteRotation modes test)))

/-- AN20 at a=1 for the genuine finite angular derivatives of the weak
solution, with the original H1 norm and a cutoff-independent constant. -/
theorem highRobinWeakInverse_first_bound (parameter : ℝ) (modes : Finset ℤ) (source : highDiskL2) :
    ‖highFiniteRotation modes (highRobinWeakInverse parameter source)‖ ≤ 2 * ‖source‖ := by
  let derivative := highFiniteRotation modes (highRobinWeakInverse parameter source)
  have coercive := (robinForm_coercivity parameter derivative).trans_eq
    ((robinForm_literal parameter derivative derivative).trans
      (congrArg Complex.re (highRobinWeakInverse_first_functional parameter modes source derivative)))
  have normBound : (-inner ℂ (highDiskBulk (highFiniteRotation modes derivative)) source.val).re ≤
      ‖derivative‖ * ‖source‖ := by
    calc
      _ ≤ ‖-inner ℂ (highDiskBulk (highFiniteRotation modes derivative)) source.val‖ := Complex.re_le_norm _
      _ = ‖inner ℂ (highDiskBulk (highFiniteRotation modes derivative)) source.val‖ := norm_neg _
      _ ≤ ‖highDiskBulk (highFiniteRotation modes derivative)‖ * ‖source.val‖ := norm_inner_le_norm _ _
      _ ≤ ‖derivative‖ * ‖source‖ :=
        mul_le_mul_of_nonneg_right (highFiniteRotation_bulk_bound modes derivative) (norm_nonneg source.val)
  have bound := coercive.trans normBound
  change (1 / 2 : ℝ) * ‖derivative‖ ^ 2 ≤ ‖derivative‖ * ‖source‖ at bound
  change ‖derivative‖ ≤ 2 * ‖source‖
  nlinarith only [bound, norm_nonneg derivative, norm_nonneg source]

end Grad.CircularHighWeak
