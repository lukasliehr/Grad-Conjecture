import GC18APGradeCompatibility
import GC18DenseInverseTransfer

noncomputable section

set_option maxHeartbeats 1200000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

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

theorem apCompleted_inverse_laws (grade : ℕ) (field : apGrade L parameters.sigma0 parameters.gamma ell 3 grade) :
    let project := apComplement L parameters.sigma0 parameters.gamma ell grade
    let action := apGaugeMap admissible gauge grade
    let inverse := apExtensionMap admissible gauge grade
    project (inverse (project field)) = inverse (project field) ∧
      inverse (action (project field)) = project field ∧ action (inverse (project field)) = project field := by
  let ordered : grade ≤ grade + 2 := Nat.le_add_right grade 2
  let inverseCoherent := (determinantInverse_estimate parameters admissible base rho epsilon gauge coherent
    constants nonnegative low bound small).actualCoherent
  apply denseComplementInverseTransfer
    (apLowering L parameters.sigma0 parameters.gamma ell ordered)
    (apLowering_denseRange L parameters.sigma0 parameters.gamma ell ordered)
    (apComplement L parameters.sigma0 parameters.gamma ell (grade + 2))
    (apGaugeMap admissible gauge (grade + 2)) (apExtensionMap admissible gauge (grade + 2))
    (apComplement L parameters.sigma0 parameters.gamma ell grade)
    (apGaugeMap admissible gauge grade) (apExtensionMap admissible gauge grade)
    (apLowering_complement L parameters.sigma0 parameters.gamma ell ordered)
    (apLowering_gauge admissible ordered gauge coherent)
    (apLowering_extension admissible ordered gauge coherent inverseCoherent)
    ?_ field
  intro input
  let projected := apComplement L parameters.sigma0 parameters.gamma ell (grade + 2) input
  have member : projected ∈ apComplementRange L parameters.sigma0 parameters.gamma ell (grade + 2) := ⟨input, rfl⟩
  have preserved := apExtensionMap_mem_high parameters admissible base rho epsilon gauge coherent constants
    nonnegative low bound small (by omega : 2 ≤ grade + 2) projected member
  have inverted := apGaugeMap_two_sided_inverse_high parameters admissible base rho epsilon gauge coherent constants
    nonnegative low bound small (by omega : 2 ≤ grade + 2) projected member
  exact ⟨(apComplementRange_mem_iff _ _ _ _ _ _).mp preserved, inverted⟩

/-- Etilde preserves the actual original AP2 complement range at every
grade, including q=0 and q=1. -/
theorem apExtensionMap_mem (grade : ℕ) (field : apGrade L parameters.sigma0 parameters.gamma ell 3 grade)
    (member : field ∈ apComplementRange L parameters.sigma0 parameters.gamma ell grade) :
    apExtensionMap admissible gauge grade field ∈ apComplementRange L parameters.sigma0 parameters.gamma ell grade := by
  apply (apComplementRange_mem_iff _ _ _ _ _ _).mpr
  have identity := (apCompleted_inverse_laws parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small grade field).1
  rw [(apComplementRange_mem_iff _ _ _ _ _ _).mp member] at identity
  exact identity

/-- The literal Etilde is the two-sided inverse of C0*C only on V=ran C0,
in the unchanged complete original AP2 norm, for every nonnegative grade. -/
theorem apGaugeMap_two_sided_inverse (grade : ℕ) (field : apGrade L parameters.sigma0 parameters.gamma ell 3 grade)
    (member : field ∈ apComplementRange L parameters.sigma0 parameters.gamma ell grade) :
    apExtensionMap admissible gauge grade (apGaugeMap admissible gauge grade field) = field ∧
      apGaugeMap admissible gauge grade (apExtensionMap admissible gauge grade field) = field := by
  have identity := (apCompleted_inverse_laws parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small grade field).2
  rw [(apComplementRange_mem_iff _ _ _ _ _ _).mp member] at identity
  exact identity

end ActualInverse

end Grad.GaugeCoefficients.Physical.RadialLedger
