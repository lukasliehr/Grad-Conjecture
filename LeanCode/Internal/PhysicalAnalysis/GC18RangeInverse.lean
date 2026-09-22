import GC18RangePreservation

noncomputable section

set_option maxHeartbeats 1500000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

/-- The nonsingular Cartesian projected full gauge on continuous physical
values. This carrier is not substituted for the original AP2 completion. -/
def cartesianGaugeMap {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (grade : ℕ) (angle : ℝ) (field : C(ClosedDisk, PhysicalValue 3)) : C(ClosedDisk, PhysicalValue 3) :=
  cartesianComplementMap ⟨fullGaugeValueAction gauge grade angle field,
    fullGaugeValueAction_continuous admissible gauge coherent grade angle field field.continuous⟩

theorem cartesianGaugeMap_mem {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (grade : ℕ) (angle : ℝ) (field : C(ClosedDisk, PhysicalValue 3)) :
    cartesianGaugeMap admissible gauge coherent grade angle field ∈ cartesianPhysicalRange :=
  ⟨_, rfl⟩

def cartesianExtensionMap {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge))
    (grade : ℕ) (angle : ℝ) (field : C(ClosedDisk, PhysicalValue 3)) : C(ClosedDisk, PhysicalValue 3) :=
  ⟨extensionValueAction admissible gauge grade angle field,
    extensionValueAction_continuous admissible gauge coherent inverseCoherent grade angle field field.continuous⟩

section ActualInverse

variable {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (base : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters base rho epsilon 6 ≤ 1)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters base rho epsilon (grade + 4))
    (small : physicalBudget parameters base rho epsilon 6 ≤ determinantLowRadius constants)

theorem cartesianExtensionMap_mem (grade : ℕ) (angle : ℝ)
    (field : C(ClosedDisk, PhysicalValue 3)) (member : field ∈ cartesianPhysicalRange) :
    cartesianExtensionMap admissible gauge coherent
      (determinantInverse_estimate parameters admissible base rho epsilon gauge coherent
        constants nonnegative low bound small).actualCoherent grade angle field ∈ cartesianPhysicalRange := by
  apply (mem_cartesianPhysicalRange_iff _).mpr
  apply ContinuousMap.ext
  intro point
  exact extensionValueAction_cartesian_fixed parameters admissible base rho epsilon gauge coherent
    constants nonnegative low bound small grade angle field member point

/-- Both identities are on the actual Cartesian C0 range, and use the
constructed determinant inverse. No ambient inverse or tangency=range is
assumed. Passage to the original weighted completion is a further boundary. -/
theorem cartesianGauge_two_sided_inverse (grade : ℕ) (angle : ℝ)
    (field : C(ClosedDisk, PhysicalValue 3)) (member : field ∈ cartesianPhysicalRange) :
    let inverseCoherent := (determinantInverse_estimate parameters admissible base rho epsilon gauge coherent
      constants nonnegative low bound small).actualCoherent
    cartesianExtensionMap admissible gauge coherent inverseCoherent grade angle
      (cartesianGaugeMap admissible gauge coherent grade angle field) = field ∧
    cartesianGaugeMap admissible gauge coherent grade angle
      (cartesianExtensionMap admissible gauge coherent inverseCoherent grade angle field) = field := by
  dsimp only
  let inverseCoherent := (determinantInverse_estimate parameters admissible base rho epsilon gauge coherent
    constants nonnegative low bound small).actualCoherent
  have tangential := cartesianRange_tangential field member
  constructor
  · apply ContinuousMap.ext
    intro point
    change coefficientPhysicalValue (complementExtensionFamily admissible gauge grade) angle point
      (cartesianComplementValue (fullGaugeValueAction gauge grade angle field) point) = field point
    rw [cartesianGauge_on_range admissible gauge coherent grade angle field member]
    exact (actualExtension_block_inverse parameters admissible base rho epsilon gauge coherent constants
      nonnegative low bound small grade angle point (field point) (tangential point)).1
  · have extensionMember := cartesianExtensionMap_mem parameters admissible base rho epsilon gauge coherent
      constants nonnegative low bound small grade angle field member
    apply ContinuousMap.ext
    intro point
    change cartesianComplementValue (fullGaugeValueAction gauge grade angle
      (cartesianExtensionMap admissible gauge coherent inverseCoherent grade angle field)) point = field point
    rw [cartesianGauge_on_range admissible gauge coherent grade angle _ extensionMember]
    exact (actualExtension_block_inverse parameters admissible base rho epsilon gauge coherent constants
      nonnegative low bound small grade angle point (field point) (tangential point)).2

end ActualInverse

end Grad.GaugeCoefficients.Physical.RadialLedger
