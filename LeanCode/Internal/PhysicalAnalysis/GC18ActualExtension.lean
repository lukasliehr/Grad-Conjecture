import GC18ExtensionValue
import GC18BoundsConsumer

noncomputable section

set_option maxHeartbeats 1400000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

theorem scalarLiftFamily_physicalValue {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension : ℕ) (family : CoefficientFamily L sigma gamma ell 1 1) (coherent : FamilyCoherent family)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (scalarLiftFamily admissible dimension family grade) angle point =
      familyMatrix family grade angle point 0 0 • ContinuousLinearMap.id ℂ (PhysicalValue dimension) := by
  apply operatorMatrix_injective
  rw [operatorMatrix_smul, operatorMatrix_one]
  apply scalarLiftFamily_matrix admissible dimension family coherent grade angle point
  ext row column
  fin_cases row
  fin_cases column
  rfl

/-- Literal AO11 multiplier realization, for the constructed coefficient
family. The inverse coherence below is discharged by the actual Neumann
estimate in the unconditional low-neighborhood consumer. -/
theorem complementExtensionFamily_action {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge))
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) (value : PhysicalValue 3) :
    coefficientPhysicalValue (complementExtensionFamily admissible gauge grade) angle point value =
      familyMatrix (determinantInverseFamily admissible gauge) grade angle point 0 0 •
        adjugateBlockValue
          (familyMatrix (muCoefficient admissible gauge) grade angle point 0 0)
          (familyMatrix (etaCoefficient admissible gauge) grade angle point 0 0)
          (familyMatrix (nuCoefficient admissible gauge) grade angle point 0 0)
          (familyMatrix (deltaCoefficient admissible gauge) grade angle point 0 0) point value := by
  unfold complementExtensionFamily composeFamily
  rw [family_physicalValue_comp admissible (scalarLiftFamily admissible 3 (determinantInverseFamily admissible gauge))
      (adjugateFamily admissible gauge) (scalarLiftFamily_coherent admissible 3 _ inverseCoherent)
      (adjugateFamily_coherent admissible gauge coherent),
    scalarLiftFamily_physicalValue admissible 3 _ inverseCoherent,
    ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    adjugateFamily_action admissible gauge coherent]

theorem radialBlockValue_smul (mu eta nu delta scalar : ℂ) (point : ClosedDisk) (value : PhysicalValue 3) :
    radialBlockValue mu eta nu delta point (scalar • value) = scalar • radialBlockValue mu eta nu delta point value := by
  apply PiLp.ext
  intro row
  fin_cases row <;> simp [radialBlockValue] <;> ring

/-- Both literal block inverse identities for the actual Etilde, using the
proved low-neighborhood determinant inverse. This is not yet an assertion
that the displayed block is C0*C on the full projected domain. -/
theorem actualExtension_block_inverse {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (field : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters field rho epsilon 6 ≤ 1)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters field rho epsilon (grade + 4))
    (small : physicalBudget parameters field rho epsilon 6 ≤ determinantLowRadius constants)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) (value : PhysicalValue 3)
    (tangential : PointwiseTangential point value) :
    let mu := familyMatrix (muCoefficient admissible gauge) grade angle point 0 0
    let eta := familyMatrix (etaCoefficient admissible gauge) grade angle point 0 0
    let nu := familyMatrix (nuCoefficient admissible gauge) grade angle point 0 0
    let delta := familyMatrix (deltaCoefficient admissible gauge) grade angle point 0 0
    let extension := coefficientPhysicalValue (complementExtensionFamily admissible gauge grade) angle point
    extension (radialBlockValue mu eta nu delta point value) = value ∧
      radialBlockValue mu eta nu delta point (extension value) = value := by
  dsimp only
  have inverseCoherent := (determinantInverse_estimate parameters admissible field rho epsilon gauge coherent
    constants nonnegative low bound small).actualCoherent
  have inverse := actualBlockDeterminantInverse parameters admissible field rho epsilon gauge coherent
    constants nonnegative low bound small grade angle point
  constructor
  · rw [complementExtensionFamily_action admissible gauge coherent inverseCoherent,
      adjugate_radialBlock _ _ _ _ point value tangential, smul_smul, inverse, one_smul]
  · rw [complementExtensionFamily_action admissible gauge coherent inverseCoherent,
      radialBlockValue_smul, radial_adjugateBlock _ _ _ _ point value tangential,
      smul_smul, inverse, one_smul]

end Grad.GaugeCoefficients.Physical.RadialLedger
