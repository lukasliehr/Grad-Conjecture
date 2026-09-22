import AKDH13ActualSourceKappaEuler

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate

section Observation
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem vectorEulerWithin_smooth (domain : Set ℝ) (unique : UniqueDiffOn ℝ domain)
    (field : ℝ → E) (rank order : ℕ)
    (smooth : ContDiffOn ℝ (order+rank : ℕ) field domain) :
    ContDiffOn ℝ order (vectorEulerWithinIteratedDerivative domain rank field) domain := by
  induction rank generalizing order with
  | zero =>
      change ContDiffOn ℝ order field domain
      simpa only [Nat.add_zero] using smooth
  | succ rank previous =>
      have earlier : ContDiffOn ℝ (order+1 : ℕ) (vectorEulerWithinIteratedDerivative domain rank field) domain :=
        previous (order+1) (by simpa only [Nat.add_assoc,Nat.add_comm 1 rank] using smooth)
      exact contDiffOn_id.smul (earlier.derivWithin unique (by simp))

/-- A bounded observation commutes with the genuine closed-collar Euler
derivative, using the already available finite-order regularity only for
fidelity, not for its quantitative estimate. -/
theorem vectorEulerWithin_observation (domain : Set ℝ) (unique : UniqueDiffOn ℝ domain)
    (field : ℝ → E) (observe : E →L[ℝ] F) (rank : ℕ)
    (smooth : ContDiffOn ℝ rank field domain) :
    EqOn (vectorEulerWithinIteratedDerivative domain rank (fun radius => observe (field radius)))
      (fun radius => observe (vectorEulerWithinIteratedDerivative domain rank field radius)) domain := by
  induction rank with
  | zero => intro radius _; rfl
  | succ rank previous =>
      have lower : ContDiffOn ℝ rank field domain := smooth.of_le (by simp)
      have earlier : ContDiffOn ℝ 1 (vectorEulerWithinIteratedDerivative domain rank field) domain :=
        vectorEulerWithin_smooth domain unique field rank 1 (by simpa only [Nat.add_comm 1 rank] using smooth)
      have same := previous lower
      intro radius inside
      change radius • derivWithin (vectorEulerWithinIteratedDerivative domain rank (fun point => observe (field point))) domain radius =
        observe (radius • derivWithin (vectorEulerWithinIteratedDerivative domain rank field) domain radius)
      rw [derivWithin_congr same (same inside)]
      have derivative := (earlier.differentiableOn (by norm_num) radius inside).hasDerivWithinAt
      have observed : HasDerivWithinAt
          (fun point => observe (vectorEulerWithinIteratedDerivative domain rank field point))
          (observe (derivWithin (vectorEulerWithinIteratedDerivative domain rank field) domain radius)) domain radius :=
        observe.hasFDerivAt.comp_hasDerivWithinAt radius derivative
      rw [observed.derivWithin (unique radius inside), map_smul]

end Observation

end Grad.OriginalCartesianTameEstimate
