import GQ1ActualProjection

noncomputable section

set_option maxHeartbeats 1200000

namespace Grad.GaugeCoefficients.Physical.GaugeTransfer

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

section ActualInverse

variable {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (base : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters base rho epsilon 6 ≤ 1)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters base rho epsilon (grade + 4))
    (small : physicalBudget parameters base rho epsilon 6 ≤ determinantLowRadius constants)

include base rho epsilon coherent constants nonnegative low bound small

theorem apCurrentProjection_range (grade : ℕ) :
    LinearMap.range (apCurrentProjection admissible gauge grade).toLinearMap =
      LinearMap.ker (apGaugeMap admissible gauge grade).toLinearMap := by
  apply le_antisymm
  · rintro _ ⟨field, rfl⟩
    exact apCurrentProjection_gauge_zero parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small grade field
  · intro field member
    refine ⟨field, ?_⟩
    change apCurrentProjection admissible gauge grade field = field
    rw [apCurrentProjection_apply, show apGaugeMap admissible gauge grade field = 0 from member, map_zero, sub_zero]

theorem apCurrentProjection_kernel (grade : ℕ) :
    LinearMap.ker (apCurrentProjection admissible gauge grade).toLinearMap =
      apComplementRange L parameters.sigma0 parameters.gamma ell grade := by
  apply le_antisymm
  · intro field member
    have same : field = apExtensionMap admissible gauge grade (apGaugeMap admissible gauge grade field) := by
      apply sub_eq_zero.mp
      exact member
    rw [same]
    exact apCurrentProjection_removed_mem parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small grade field
  · intro field member
    exact apCurrentProjection_kills_complement parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small grade field member

def apRangeForward (grade : ℕ) :
    LinearMap.range (apCircleProjection L parameters.sigma0 parameters.gamma ell grade).toLinearMap →L[ℂ]
      LinearMap.range (apCurrentProjection admissible gauge grade).toLinearMap :=
  ((apCurrentProjection admissible gauge grade).comp
    (LinearMap.range (apCircleProjection L parameters.sigma0 parameters.gamma ell grade).toLinearMap).subtypeL).codRestrict
      _ (fun field => ⟨field.val, rfl⟩)

def apRangeBackward (grade : ℕ) :
    LinearMap.range (apCurrentProjection admissible gauge grade).toLinearMap →L[ℂ]
      LinearMap.range (apCircleProjection L parameters.sigma0 parameters.gamma ell grade).toLinearMap :=
  ((apCircleProjection L parameters.sigma0 parameters.gamma ell grade).comp
    (LinearMap.range (apCurrentProjection admissible gauge grade).toLinearMap).subtypeL).codRestrict
      _ (fun field => ⟨field.val, rfl⟩)

theorem apRangeBackward_forward (grade : ℕ)
    (field : LinearMap.range (apCircleProjection L parameters.sigma0 parameters.gamma ell grade).toLinearMap) :
    apRangeBackward parameters admissible gauge grade (apRangeForward parameters admissible gauge grade field) = field := by
  apply Subtype.ext
  change apCircleProjection L parameters.sigma0 parameters.gamma ell grade (apCurrentProjection admissible gauge grade field.val) = field.val
  rw [apCurrentProjection_circle_left parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small]
  rcases field.property with ⟨original, equality⟩
  rw [← equality]
  exact apCircleProjection_idempotent L parameters.sigma0 parameters.gamma ell grade original

theorem apRangeForward_backward (grade : ℕ)
    (field : LinearMap.range (apCurrentProjection admissible gauge grade).toLinearMap) :
    apRangeForward parameters admissible gauge grade (apRangeBackward parameters admissible gauge grade field) = field := by
  apply Subtype.ext
  change apCurrentProjection admissible gauge grade (apCircleProjection L parameters.sigma0 parameters.gamma ell grade field.val) = field.val
  rw [apCurrentProjection_circle_right parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small]
  rcases field.property with ⟨original, equality⟩
  rw [← equality]
  exact apCurrentProjection_idempotent parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small grade original

/-- The actual same-grade AP2 range isomorphism: Q_a forward, the fixed
Q0 backward. This is not yet the compensated-state graph isomorphism. -/
def apRangeEquivalence (grade : ℕ) :
    LinearMap.range (apCircleProjection L parameters.sigma0 parameters.gamma ell grade).toLinearMap ≃L[ℂ]
      LinearMap.range (apCurrentProjection admissible gauge grade).toLinearMap where
  toLinearEquiv := {
    toLinearMap := (apRangeForward parameters admissible gauge grade).toLinearMap
    invFun := apRangeBackward parameters admissible gauge grade
    left_inv := apRangeBackward_forward parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small grade
    right_inv := apRangeForward_backward parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small grade }
  continuous_toFun := (apRangeForward parameters admissible gauge grade).continuous
  continuous_invFun := (apRangeBackward parameters admissible gauge grade).continuous

end ActualInverse

end Grad.GaugeCoefficients.Physical.GaugeTransfer
