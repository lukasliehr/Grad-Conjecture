import GC18APMultiplierValue

noncomputable section

set_option maxHeartbeats 1200000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

def apGaugeMap {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) :
    apGrade L sigma gamma ell 3 grade →L[ℂ] apGrade L sigma gamma ell 3 grade :=
  (apComplement L sigma gamma ell grade).comp (apMultiplier admissible (fullGaugeFamily gauge grade))

def apExtensionMap {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) :
    apGrade L sigma gamma ell 3 grade →L[ℂ] apGrade L sigma gamma ell 3 grade :=
  apMultiplier admissible (complementExtensionFamily admissible gauge grade)

theorem apGaugeMap_physical {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    {grade : ℕ} (large : 2 ≤ grade) (angle : ℝ) (field : apGrade L sigma gamma ell 3 grade) :
    apPhysicalValue admissible large angle (apGaugeMap admissible gauge grade field) =
      cartesianGaugeMap admissible gauge coherent grade angle (apPhysicalValue admissible large angle field) := by
  change apPhysicalValue admissible large angle (apComplement L sigma gamma ell grade
    (apMultiplier admissible (fullGaugeFamily gauge grade) field)) = _
  rw [apComplement_physical, apMultiplier_physical]
  rfl

theorem apExtensionMap_physical {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge))
    {grade : ℕ} (large : 2 ≤ grade) (angle : ℝ) (field : apGrade L sigma gamma ell 3 grade) :
    apPhysicalValue admissible large angle (apExtensionMap admissible gauge grade field) =
      cartesianExtensionMap admissible gauge coherent inverseCoherent grade angle (apPhysicalValue admissible large angle field) := by
  change apPhysicalValue admissible large angle
    (apMultiplier admissible (complementExtensionFamily admissible gauge grade) field) = _
  rw [apMultiplier_physical]
  rfl

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

theorem apExtensionMap_mem_high {grade : ℕ} (large : 2 ≤ grade)
    (field : apGrade L parameters.sigma0 parameters.gamma ell 3 grade)
    (member : field ∈ apComplementRange L parameters.sigma0 parameters.gamma ell grade) :
    apExtensionMap admissible gauge grade field ∈ apComplementRange L parameters.sigma0 parameters.gamma ell grade := by
  let inverseCoherent := (determinantInverse_estimate parameters admissible base rho epsilon gauge coherent
    constants nonnegative low bound small).actualCoherent
  apply (apComplementRange_physical admissible large _).mpr
  intro angle
  rw [apExtensionMap_physical admissible gauge coherent inverseCoherent large angle field]
  exact cartesianExtensionMap_mem parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small
    grade angle _ ((apComplementRange_physical admissible large field).mp member angle)

/-- Actual two-sided inverse on the original completed V=ran C0, for
Sobolev grades admitting the faithful continuous realization. -/
theorem apGaugeMap_two_sided_inverse_high {grade : ℕ} (large : 2 ≤ grade)
    (field : apGrade L parameters.sigma0 parameters.gamma ell 3 grade)
    (member : field ∈ apComplementRange L parameters.sigma0 parameters.gamma ell grade) :
    apExtensionMap admissible gauge grade (apGaugeMap admissible gauge grade field) = field ∧
      apGaugeMap admissible gauge grade (apExtensionMap admissible gauge grade field) = field := by
  let inverseCoherent := (determinantInverse_estimate parameters admissible base rho epsilon gauge coherent
    constants nonnegative low bound small).actualCoherent
  have physicalMember (angle : ℝ) := (apComplementRange_physical admissible large field).mp member angle
  constructor
  · apply apPhysicalValue_ext admissible large
    intro angle
    rw [apExtensionMap_physical admissible gauge coherent inverseCoherent large,
      apGaugeMap_physical admissible gauge coherent large]
    exact (cartesianGauge_two_sided_inverse parameters admissible base rho epsilon gauge coherent constants
      nonnegative low bound small grade angle _ (physicalMember angle)).1
  · apply apPhysicalValue_ext admissible large
    intro angle
    rw [apGaugeMap_physical admissible gauge coherent large,
      apExtensionMap_physical admissible gauge coherent inverseCoherent large]
    exact (cartesianGauge_two_sided_inverse parameters admissible base rho epsilon gauge coherent constants
      nonnegative low bound small grade angle _ (physicalMember angle)).2

end ActualInverse

end Grad.GaugeCoefficients.Physical.RadialLedger
