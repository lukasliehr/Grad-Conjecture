import GC18Determinant

noncomputable section

set_option maxHeartbeats 1400000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Neumann Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.InverseAllocation

def determinantInverseConstant (constants : ℕ → ℝ) (grade : ℕ) : ℝ :=
  inverseNormConstant (determinantConstant constants) 6 grade 1 (1 / 2)

theorem determinantInverseConstant_nonnegative (constants : ℕ → ℝ) (grade : ℕ) :
    0 ≤ determinantInverseConstant constants grade :=
  inverseNormConstant_nonnegative _ (determinantConstant_nonnegative constants) 6 grade (by norm_num) (by norm_num)

theorem determinantInverse_estimate {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (field : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters field rho epsilon 6 ≤ 1)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters field rho epsilon (grade + 4))
    (small : physicalBudget parameters field rho epsilon 6 ≤ determinantLowRadius constants) :
    FamilyEstimate parameters field rho epsilon 6 (unitProfile (determinantInverseConstant constants))
      (determinantInverseFamily admissible gauge) (identityFamily L parameters.sigma0 parameters.gamma ell 1) := by
  have determinantEstimate := determinant_estimate parameters admissible field rho epsilon gauge coherent constants nonnegative low bound
  have inputCoherent : FamilyCoherent (determinantInverseInput admissible gauge) :=
    (identityFamily_coherent L parameters.sigma0 parameters.gamma ell 1).sub determinantEstimate.actualCoherent
  have margin := determinant_base_margin parameters admissible field rho epsilon gauge coherent constants nonnegative low bound small
  have inputBound (grade : ℕ) : ‖determinantInverseInput admissible gauge grade‖ ≤
      determinantConstant constants grade * physicalBudget parameters field rho epsilon (6 + grade) := by
    change ‖identityFamily L parameters.sigma0 parameters.gamma ell 1 grade - determinantFamily admissible gauge grade‖ ≤ _
    rw [norm_sub_rev]
    simpa only [determinantConstant, Nat.add_comm] using determinantEstimate.absoluteBound grade
  refine ⟨inverseFamily_coherent admissible (by norm_num) _ inputCoherent (1 / 2) margin (by norm_num),
    identityFamily_coherent L parameters.sigma0 parameters.gamma ell 1,
    fun _ => Nat.cast_nonneg _, determinantInverseConstant_nonnegative constants,
    identityFamily_norm_le L parameters.sigma0 parameters.gamma ell 1, ?_⟩
  intro grade
  exact inverse_norm_one_high parameters admissible 6 grade field rho epsilon 1 (1 / 2)
    (by norm_num) (by norm_num) low (by norm_num) _ inputCoherent (determinantConstant constants)
    (determinantConstant_nonnegative constants) inputBound margin

/-- Both pointwise scalar inverse identities, obtained from the actual
Neumann family on the proved, grade-independent determinant margin. -/
theorem determinantInverse_two_sided {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (field : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters field rho epsilon 6 ≤ 1)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters field rho epsilon (grade + 4))
    (small : physicalBudget parameters field rho epsilon 6 ≤ determinantLowRadius constants)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (determinantFamily admissible gauge) grade angle point *
      familyMatrix (determinantInverseFamily admissible gauge) grade angle point = 1 ∧
    familyMatrix (determinantInverseFamily admissible gauge) grade angle point *
      familyMatrix (determinantFamily admissible gauge) grade angle point = 1 := by
  have determinantCoherent := (determinant_estimate parameters admissible field rho epsilon gauge coherent constants nonnegative low bound).actualCoherent
  have inputCoherent : FamilyCoherent (determinantInverseInput admissible gauge) :=
    (identityFamily_coherent L parameters.sigma0 parameters.gamma ell 1).sub determinantCoherent
  have margin := determinant_base_margin parameters admissible field rho epsilon gauge coherent constants nonnegative low bound small
  have identities := analyticCapCoefficientNeumannInverse_pointwiseIdentification admissible (by norm_num : 0 < 1)
    (determinantInverseInput admissible gauge 0) (1 / 2) margin (by norm_num) angle point
  have inputValue : fourierEvaluation (determinantInverseInput admissible gauge 0) angle point =
      ContinuousLinearMap.id ℂ (PhysicalValue 1) -
        coefficientPhysicalValue (determinantFamily admissible gauge grade) angle point := by
    rw [← coherent_physicalValue _ inputCoherent grade]
    change coefficientPhysicalValue (identityFamily L parameters.sigma0 parameters.gamma ell 1 grade -
      determinantFamily admissible gauge grade) angle point = _
    rw [family_physicalValue_sub admissible (identityFamily L parameters.sigma0 parameters.gamma ell 1)
      (determinantFamily admissible gauge)
      (identityFamily_coherent L parameters.sigma0 parameters.gamma ell 1) determinantCoherent grade angle point]
    change coefficientPhysicalValue (gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade 1)
      angle point - _ = _
    rw [identityFamily_physicalValue]
  rw [inputValue, sub_sub_cancel] at identities
  have inverseValue := inverseFamily_physicalValue admissible (by norm_num : 0 < 1) _
    inputCoherent (1 / 2) margin (by norm_num) grade angle point
  unfold familyMatrix determinantInverseFamily
  rw [inverseValue]
  exact ⟨(operatorMatrix_comp _ _).symm.trans ((congrArg operatorMatrix identities.1).trans (operatorMatrix_one 1)),
    (operatorMatrix_comp _ _).symm.trans ((congrArg operatorMatrix identities.2).trans (operatorMatrix_one 1))⟩

end Grad.GaugeCoefficients.Physical.RadialLedger
