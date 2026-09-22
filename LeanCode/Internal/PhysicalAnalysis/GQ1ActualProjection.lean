import GC18Consumer

noncomputable section

set_option maxHeartbeats 1200000

namespace Grad.GaugeCoefficients.Physical.GaugeTransfer

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

/-- The fixed circle projection on the unchanged original AP2 graph. -/
def apCircleProjection (L sigma gamma ell : ℝ) (grade : ℕ) :
    apGrade L sigma gamma ell 3 grade →L[ℂ] apGrade L sigma gamma ell 3 grade :=
  ContinuousLinearMap.id ℂ _ - apComplement L sigma gamma ell grade

/-- Literal AO17, using the actual completed C0*C and the constructed
smooth adjugate multiplier. It is not an inverse on the ambient space. -/
def apCurrentProjection {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) :
    apGrade L sigma gamma ell 3 grade →L[ℂ] apGrade L sigma gamma ell 3 grade :=
  ContinuousLinearMap.id ℂ _ - (apExtensionMap admissible gauge grade).comp (apGaugeMap admissible gauge grade)

theorem apCircleProjection_apply (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : apGrade L sigma gamma ell 3 grade) :
    apCircleProjection L sigma gamma ell grade field = field - apComplement L sigma gamma ell grade field := rfl

theorem apCurrentProjection_apply {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) (field : apGrade L sigma gamma ell 3 grade) :
    apCurrentProjection admissible gauge grade field =
      field - apExtensionMap admissible gauge grade (apGaugeMap admissible gauge grade field) := rfl

theorem apGaugeMap_mem {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) (field : apGrade L sigma gamma ell 3 grade) :
    apGaugeMap admissible gauge grade field ∈ apComplementRange L sigma gamma ell grade :=
  ⟨apMultiplier admissible (fullGaugeFamily gauge grade) field, rfl⟩

theorem apCircleProjection_idempotent (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : apGrade L sigma gamma ell 3 grade) :
    apCircleProjection L sigma gamma ell grade (apCircleProjection L sigma gamma ell grade field) =
      apCircleProjection L sigma gamma ell grade field := by
  simp only [apCircleProjection_apply, map_sub, apComplement_idempotent, sub_self, sub_zero]

theorem apCircleProjection_complement (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : apGrade L sigma gamma ell 3 grade) :
    apCircleProjection L sigma gamma ell grade (apComplement L sigma gamma ell grade field) = 0 := by
  rw [apCircleProjection_apply, apComplement_idempotent, sub_self]

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

theorem apCurrentProjection_removed_mem (grade : ℕ)
    (field : apGrade L parameters.sigma0 parameters.gamma ell 3 grade) :
    apExtensionMap admissible gauge grade (apGaugeMap admissible gauge grade field) ∈
      apComplementRange L parameters.sigma0 parameters.gamma ell grade :=
  apExtensionMap_mem parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small
    grade _ (apGaugeMap_mem admissible gauge grade field)

theorem apCurrentProjection_gauge_zero (grade : ℕ)
    (field : apGrade L parameters.sigma0 parameters.gamma ell 3 grade) :
    apGaugeMap admissible gauge grade (apCurrentProjection admissible gauge grade field) = 0 := by
  rw [apCurrentProjection_apply, map_sub]
  rw [(apGaugeMap_two_sided_inverse parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small
    grade _ (apGaugeMap_mem admissible gauge grade field)).2, sub_self]

theorem apCurrentProjection_kills_complement (grade : ℕ)
    (field : apGrade L parameters.sigma0 parameters.gamma ell 3 grade)
    (member : field ∈ apComplementRange L parameters.sigma0 parameters.gamma ell grade) :
    apCurrentProjection admissible gauge grade field = 0 := by
  rw [apCurrentProjection_apply,
    (apGaugeMap_two_sided_inverse parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small
      grade field member).1, sub_self]

theorem apCurrentProjection_idempotent (grade : ℕ)
    (field : apGrade L parameters.sigma0 parameters.gamma ell 3 grade) :
    apCurrentProjection admissible gauge grade (apCurrentProjection admissible gauge grade field) =
      apCurrentProjection admissible gauge grade field := by
  rw [apCurrentProjection_apply,
    apCurrentProjection_gauge_zero parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small,
    map_zero, sub_zero]

theorem apCurrentProjection_circle_right (grade : ℕ)
    (field : apGrade L parameters.sigma0 parameters.gamma ell 3 grade) :
    apCurrentProjection admissible gauge grade (apCircleProjection L parameters.sigma0 parameters.gamma ell grade field) =
      apCurrentProjection admissible gauge grade field := by
  have killed : apCurrentProjection admissible gauge grade (apComplement L parameters.sigma0 parameters.gamma ell grade field) = 0 :=
    apCurrentProjection_kills_complement parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small
      grade (apComplement L parameters.sigma0 parameters.gamma ell grade field) ⟨field, rfl⟩
  rw [apCircleProjection_apply, map_sub, killed, sub_zero]

theorem apCurrentProjection_circle_left (grade : ℕ)
    (field : apGrade L parameters.sigma0 parameters.gamma ell 3 grade) :
    apCircleProjection L parameters.sigma0 parameters.gamma ell grade (apCurrentProjection admissible gauge grade field) =
      apCircleProjection L parameters.sigma0 parameters.gamma ell grade field := by
  rw [apCurrentProjection_apply, map_sub]
  have member := apCurrentProjection_removed_mem parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small grade field
  have fixed := (apComplementRange_mem_iff L parameters.sigma0 parameters.gamma ell grade _).mp member
  rw [apCircleProjection_apply L parameters.sigma0 parameters.gamma ell grade
    (apExtensionMap admissible gauge grade (apGaugeMap admissible gauge grade field)), fixed, sub_self, sub_zero]

end ActualInverse

end Grad.GaugeCoefficients.Physical.GaugeTransfer
