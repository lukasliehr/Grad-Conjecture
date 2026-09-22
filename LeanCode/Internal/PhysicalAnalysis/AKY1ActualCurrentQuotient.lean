import GQC66PhysicalCoreConsumer
import GQF14CircularDomain
import ANP5GradientAndCurl
import ANT2ScalarCommutators
import ANV1HelicityAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.CartesianUncompressed
open Grad.NonlinearDivision Grad.GaugeCoefficients.Physical.Allocation
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualAngularInverse Grad.ActualNonexceptionalInverse Grad.RawCircularSectors

variable {L sigma gamma ell : ℝ}

/-- ER3 uses the actual fixed quotient and the actual current-gauge projection.
No axis-flatness assumption is involved. -/
theorem actualCurrent_quotient_recover
    (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge))
    (laws : ∀ grade, ActualProjectionLaws admissible gauge grade)
    (field : APSmooth L sigma gamma ell 3)
    (currentGauge : apSmoothGauge admissible gauge coherent field = 0) :
    apSmoothCurrent admissible gauge coherent inverseCoherent
      (apSmoothCircle L sigma gamma ell field) = field :=
  (apSmoothCurrent_circle_right admissible gauge coherent inverseCoherent laws field).trans
    (apSmoothCurrent_fixed admissible gauge coherent inverseCoherent field currentGauge)

theorem actualQuotient_fixedGauge
    (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) :
    apSmoothComplement L sigma gamma ell (apSmoothCircle L sigma gamma ell field) = 0 :=
  (apSmoothCircle_fixed_iff _).mp (apSmoothCircle_idempotent admissible field)

theorem actualQuotient_componentGauges
    (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) :
    apSmoothTangential L sigma gamma ell
      (apSmoothPlanar L sigma gamma ell (apSmoothCircle L sigma gamma ell field)) = 0 ∧
    apSmoothAngularMean L sigma gamma ell 1
      (apSmoothScalar L sigma gamma ell (apSmoothCircle L sigma gamma ell field)) = 0 := by
  have gauge := actualQuotient_fixedGauge admissible field
  constructor
  · exact (apSmoothPlanar_complement admissible _).symm.trans
      ((congrArg (apSmoothPlanar L sigma gamma ell) gauge).trans (map_zero _))
  · exact (apSmoothScalar_complement admissible _).symm.trans
      ((congrArg (apSmoothScalar L sigma gamma ell) gauge).trans (map_zero _))

end Grad.CartesianUncompressed
