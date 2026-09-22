import GC18ActualGaugeAction

noncomputable section

set_option maxHeartbeats 1700000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

theorem cartesianRange_profiles (field : C(ClosedDisk, PhysicalValue 3)) (member : field ∈ cartesianPhysicalRange) :
    ∃ first second : ClosedDisk → ℂ, IsDiskRadial first ∧ IsDiskRadial second ∧ complementProfile first second = field := by
  let first := fun point => (radiusScalar point)⁻¹ * closedAngularMean (fun other => storedTangentDot other (field other)) point
  let second := closedAngularMean (fun point => field point 2)
  refine ⟨first, second, fixedComplementValue_profile_first_radial field, closedAngularMean_radial _, ?_⟩
  funext point
  change fixedComplementValue field point = field point
  rw [← cartesianComplementValue_eq_polar field field.continuous point]
  exact congrArg (fun mapping : C(ClosedDisk, PhysicalValue 3) => mapping point)
    ((mem_cartesianPhysicalRange_iff field).mp member)

theorem complementProfile_tangential (first second : ClosedDisk → ℂ) (point : ClosedDisk) :
    PointwiseTangential point (complementProfile first second point) := by
  unfold PointwiseTangential
  simp [complementProfile, storedTangent, storedScalar]
  ring

theorem cartesianRange_tangential (field : C(ClosedDisk, PhysicalValue 3)) (member : field ∈ cartesianPhysicalRange)
    (point : ClosedDisk) : PointwiseTangential point (field point) := by
  obtain ⟨first, second, _, _, profile⟩ := cartesianRange_profiles field member
  rw [← profile]
  exact complementProfile_tangential first second point

def extensionValueAction {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) (angle : ℝ)
    (field : ClosedDisk → PhysicalValue 3) (point : ClosedDisk) : PhysicalValue 3 :=
  coefficientPhysicalValue (complementExtensionFamily admissible gauge grade) angle point (field point)

theorem complementExtensionFamily_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge)) :
    FamilyCoherent (complementExtensionFamily admissible gauge) :=
  (scalarLiftFamily_coherent admissible 3 _ inverseCoherent).comp admissible (adjugateFamily_coherent admissible gauge coherent)

theorem extensionValueAction_continuous {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge))
    (grade : ℕ) (angle : ℝ) (field : ClosedDisk → PhysicalValue 3) (continuous : Continuous field) :
    Continuous (extensionValueAction admissible gauge grade angle field) :=
  (coefficientPhysicalValue_continuous admissible (complementExtensionFamily admissible gauge)
    (complementExtensionFamily_coherent admissible gauge coherent inverseCoherent) grade angle).clm_apply continuous

theorem radialAdjugate_cartesian_fixed (mu eta nu delta inverse : ClosedDisk → ℂ)
    (muRadial : IsDiskRadial mu) (etaRadial : IsDiskRadial eta) (nuRadial : IsDiskRadial nu)
    (deltaRadial : IsDiskRadial delta) (inverseRadial : IsDiskRadial inverse)
    (field : C(ClosedDisk, PhysicalValue 3)) (member : field ∈ cartesianPhysicalRange)
    (output : ClosedDisk → PhysicalValue 3) (outputContinuous : Continuous output)
    (action : ∀ point, output point = inverse point •
      adjugateBlockValue (mu point) (eta point) (nu point) (delta point) point (field point))
    (point : ClosedDisk) : cartesianComplementValue output point = output point := by
  obtain ⟨first, second, firstRadial, secondRadial, profile⟩ := cartesianRange_profiles field member
  let newFirst := fun other => inverse other * (delta other * first other - eta other * second other)
  let newSecond := fun other => inverse other * (-nu other * radiusScalar other * first other + mu other * second other)
  have newFirstRadial : IsDiskRadial newFirst := inverseRadial.mul ((deltaRadial.mul firstRadial).sub (etaRadial.mul secondRadial))
  have newSecondRadial : IsDiskRadial newSecond := inverseRadial.mul
    (((nuRadial.neg.mul radiusScalar_rotation).mul firstRadial).add (muRadial.mul secondRadial))
  have outputProfile : output = complementProfile newFirst newSecond := by
    funext other
    rw [action other, ← profile, adjugateBlockValue_profile, complementProfile_smul]
    rfl
  rw [outputProfile] at outputContinuous ⊢
  exact radialProfile_cartesian_fixed newFirst newSecond newFirstRadial newSecondRadial outputContinuous point

theorem extensionValueAction_cartesian_fixed {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (base : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters base rho epsilon 6 ≤ 1)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters base rho epsilon (grade + 4))
    (small : physicalBudget parameters base rho epsilon 6 ≤ determinantLowRadius constants)
    (grade : ℕ) (angle : ℝ) (field : C(ClosedDisk, PhysicalValue 3)) (member : field ∈ cartesianPhysicalRange)
    (point : ClosedDisk) :
    cartesianComplementValue (extensionValueAction admissible gauge grade angle field) point =
      extensionValueAction admissible gauge grade angle field point := by
  have inverseCoherent := (determinantInverse_estimate parameters admissible base rho epsilon gauge coherent
    constants nonnegative low bound small).actualCoherent
  apply radialAdjugate_cartesian_fixed
    (fun other => familyMatrix (muCoefficient admissible gauge) grade angle other 0 0)
    (fun other => familyMatrix (etaCoefficient admissible gauge) grade angle other 0 0)
    (fun other => familyMatrix (nuCoefficient admissible gauge) grade angle other 0 0)
    (fun other => familyMatrix (deltaCoefficient admissible gauge) grade angle other 0 0)
    (fun other => familyMatrix (determinantInverseFamily admissible gauge) grade angle other 0 0)
    (muCoefficient_entry_radial admissible gauge coherent grade angle)
    (etaCoefficient_entry_radial admissible gauge coherent grade angle)
    (nuCoefficient_entry_radial admissible gauge coherent grade angle)
    (deltaCoefficient_entry_radial admissible gauge coherent grade angle)
    (determinantInverseFamily_entry_radial parameters admissible base rho epsilon gauge coherent
      constants nonnegative low bound small grade angle) field member _
    (extensionValueAction_continuous admissible gauge coherent inverseCoherent grade angle field field.continuous)
  intro other
  exact complementExtensionFamily_action admissible gauge coherent inverseCoherent grade angle other (field other)

end Grad.GaugeCoefficients.Physical.RadialLedger
