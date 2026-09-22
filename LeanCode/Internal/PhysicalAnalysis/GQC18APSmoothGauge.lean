import GQC17APLiteralCarrier

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.GaugeTransfer

def apSmoothMap {L sigma gamma ell : ℝ} {input output : ℕ}
    (maps : ∀ grade : ℕ, apGrade L sigma gamma ell input grade →L[ℂ] apGrade L sigma gamma ell output grade)
    (compatible : ∀ (low high : ℕ) (ordered : low ≤ high) (field : apGrade L sigma gamma ell input high),
      apLowering L sigma gamma ell ordered (maps high field) = maps low (apLowering L sigma gamma ell ordered field)) :
    APSmooth L sigma gamma ell input →ₗ[ℂ] APSmooth L sigma gamma ell output where
  toFun field := ⟨fun grade => maps grade (field.val grade), fun low high ordered => by
    rw [compatible low high ordered, field.property low high ordered]⟩
  map_add' first second := by apply Subtype.ext; funext grade; exact (maps grade).map_add (first.val grade) (second.val grade)
  map_smul' scalar field := by apply Subtype.ext; funext grade; exact (maps grade).map_smul scalar (field.val grade)

def apSmoothComplement (L sigma gamma ell : ℝ) :
    APSmooth L sigma gamma ell 3 →ₗ[ℂ] APSmooth L sigma gamma ell 3 :=
  apSmoothMap (apComplement L sigma gamma ell) (fun _low _high ordered field =>
    apLowering_complement L sigma gamma ell ordered field)

def apSmoothCircle (L sigma gamma ell : ℝ) :
    APSmooth L sigma gamma ell 3 →ₗ[ℂ] APSmooth L sigma gamma ell 3 :=
  LinearMap.id - apSmoothComplement L sigma gamma ell

def apSmoothMultiplier {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (coefficient : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent coefficient) :
    APSmooth L sigma gamma ell input →ₗ[ℂ] APSmooth L sigma gamma ell output :=
  apSmoothMap (fun grade => apMultiplier admissible (coefficient grade))
    (fun _low _high ordered field => apLowering_multiplier admissible ordered coefficient coherent field)

def apSmoothGauge {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge) :
    APSmooth L sigma gamma ell 3 →ₗ[ℂ] APSmooth L sigma gamma ell 3 :=
  apSmoothMap (apGaugeMap admissible gauge) (fun _low _high ordered field =>
    apLowering_gauge admissible ordered gauge coherent field)

def apSmoothExtension {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge)) :
    APSmooth L sigma gamma ell 3 →ₗ[ℂ] APSmooth L sigma gamma ell 3 :=
  apSmoothMap (apExtensionMap admissible gauge) (fun _low _high ordered field =>
    apLowering_extension admissible ordered gauge coherent inverseCoherent field)

/-- The actual AP2 projection acting on the genuine all-grade smooth
carrier. Its smoothness follows from reconstruction, not a finite-band claim. -/
def apSmoothCurrent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge)) :
    APSmooth L sigma gamma ell 3 →ₗ[ℂ] APSmooth L sigma gamma ell 3 :=
  LinearMap.id - (apSmoothExtension admissible gauge coherent inverseCoherent).comp (apSmoothGauge admissible gauge coherent)

theorem apSmoothCurrent_grade {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge))
    (field : APSmooth L sigma gamma ell 3) (grade : ℕ) :
    apSmoothGrade L sigma gamma ell 3 grade (apSmoothCurrent admissible gauge coherent inverseCoherent field) =
      apCurrentProjection admissible gauge grade (apSmoothGrade L sigma gamma ell 3 grade field) := rfl

theorem apSmoothCircle_grade {L sigma gamma ell : ℝ}
    (field : APSmooth L sigma gamma ell 3) (grade : ℕ) :
    apSmoothGrade L sigma gamma ell 3 grade (apSmoothCircle L sigma gamma ell field) =
      apCircleProjection L sigma gamma ell grade (apSmoothGrade L sigma gamma ell 3 grade field) := rfl

end Grad.GaugeCoefficients.Physical.Compensated
