import GC18APL2Product
import GC18APLowering

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

theorem apLowering_L2 {dimension low high : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (ordered : low ≤ high) (angle : ℝ)
    (field : apGrade L sigma gamma ell dimension high) :
    apL2PhysicalValue admissible angle (apLowering L sigma gamma ell ordered field) = apL2PhysicalValue admissible angle field := by
  let first := (apL2PhysicalValue (dimension := dimension) (grade := low) admissible angle).comp (apLowering L sigma gamma ell ordered)
  let second := apL2PhysicalValue (dimension := dimension) (grade := high) admissible angle
  have equality : first = second := by
    apply apFiniteGenerator_ext L sigma gamma ell first second
    intro cell core
    change apL2PhysicalValue admissible angle (apLowering L sigma gamma ell ordered
      (apFiniteInto L sigma gamma ell (Finsupp.single cell core))) = _
    rw [apLowering_core, apL2PhysicalValue_single]
    exact (apL2PhysicalValue_single admissible angle cell core).symm
  change first field = second field
  rw [equality]

theorem cMapCoefficient_coherent {input output : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (family : CoefficientFamily L sigma gamma ell input output)
    (coherent : FamilyCoherent family) (first second : ℕ) (angle : ℝ) :
    cMapCoefficient admissible first input output angle (family first) =
      cMapCoefficient admissible second input output angle (family second) := by
  apply ContinuousMap.ext
  intro point
  rw [cMapCoefficient_apply, cMapCoefficient_apply, coherent_physicalValue family coherent,
    coherent_physicalValue family coherent]

theorem apLowering_multiplier {input output low high : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (ordered : low ≤ high)
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (field : apGrade L sigma gamma ell input high) :
    apLowering L sigma gamma ell ordered (apMultiplier admissible (family high) field) =
      apMultiplier admissible (family low) (apLowering L sigma gamma ell ordered field) := by
  apply apL2PhysicalValue_ext admissible
  intro angle
  rw [apLowering_L2, apMultiplier_L2, apMultiplier_L2, apLowering_L2,
    cMapCoefficient_coherent admissible family coherent high low angle]

theorem apLowering_gauge {low high : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (ordered : low ≤ high)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (field : apGrade L sigma gamma ell 3 high) :
    apLowering L sigma gamma ell ordered (apGaugeMap admissible gauge high field) =
      apGaugeMap admissible gauge low (apLowering L sigma gamma ell ordered field) := by
  change apLowering L sigma gamma ell ordered (apComplement L sigma gamma ell high
    (apMultiplier admissible (fullGaugeFamily gauge high) field)) = _
  rw [apLowering_complement, apLowering_multiplier admissible ordered (fullGaugeFamily gauge) (fullGaugeFamily_coherent gauge coherent)]
  rfl

theorem apLowering_extension {low high : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (ordered : low ≤ high)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge))
    (field : apGrade L sigma gamma ell 3 high) :
    apLowering L sigma gamma ell ordered (apExtensionMap admissible gauge high field) =
      apExtensionMap admissible gauge low (apLowering L sigma gamma ell ordered field) :=
  apLowering_multiplier admissible ordered (complementExtensionFamily admissible gauge)
    (complementExtensionFamily_coherent admissible gauge coherent inverseCoherent) field

end Grad.GaugeCoefficients.Physical.RadialLedger
