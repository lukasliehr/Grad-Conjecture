import GSP1OriginalGaugeFamily
import GQ8PhysicalScaling

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.ActualGaugeSigmaPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.GaugeTransfer

theorem originalSeedDerivative_matrix (parameters : PhaseParameters) (L rho alpha delta parameter : ℝ)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (originalSeedDerivative parameters L rho alpha delta parameter) grade angle point =
      ((L : ℂ)⁻¹) • operatorMatrix (deriv (harmonicSeedOperator rho alpha delta parameter) angle) := by
  have scaled : familyMatrix (originalSeedDerivative parameters L rho alpha delta parameter) grade angle point =
      ((L : ℂ)⁻¹) • familyMatrix
        (fun q => seedDerivativeCoefficient (unitDiskAdmissible parameters) q rho alpha delta parameter)
        grade angle point := by
    unfold familyMatrix originalSeedDerivative
    rw [family_physicalValue_smul (unitDiskAdmissible parameters) _
      (seedDerivativeFamily_coherent (unitDiskAdmissible parameters) rho alpha delta parameter), operatorMatrix_smul]
  rw [scaled, seedDerivativeFamily_matrix]
  change ((L : ℂ)⁻¹) • actualScaledSeedDerivative (admissible := unitDiskAdmissible parameters)
    (rho := rho) (alpha := alpha) (delta := delta) (parameter := parameter) angle point = _
  rw [actualScaledSeedDerivative_formula]
  simp only [div_self (by norm_num : (1 : ℝ) ≠ 0), Complex.ofReal_one, one_smul]

theorem originalGauge_coherent (parameters : PhaseParameters) (L rho alpha delta parameter epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L) :
    FamilyCoherent (originalGauge parameters L rho alpha delta parameter epsilon field) :=
  gaugeFamily_coherent (unitDiskAdmissible parameters) _ _ _
    ((identityFamily_coherent 1 parameters.sigma0 parameters.gamma 1 2).add
      (seedDeviationFamily_coherent (unitDiskAdmissible parameters) rho alpha delta parameter))
    (originalSeedDerivative_coherent parameters L rho alpha delta parameter)
    (originalInverseFamily_coherent parameters L epsilon field
      (originalCoefficient_low_margin parameters L rho epsilon field low).2.2)

theorem referenceGauge_coherent (parameters : PhaseParameters) : FamilyCoherent (referenceGauge parameters) :=
  gaugeFamily_coherent (unitDiskAdmissible parameters) _ _ _
    (identityFamily_coherent 1 parameters.sigma0 parameters.gamma 1 2)
    (zeroFamily_coherent 1 parameters.sigma0 parameters.gamma 1 2 2)
    (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 referenceFrame)

/-- Literal stacked Cartesian gauge rows on the original physical disk.
The toroidal seed covector is eT+L^-1 iota M'Y, at the same point. -/
def originalPhysicalGaugeMatrix (parameters : PhaseParameters) (L rho alpha delta parameter epsilon : ℝ)
    (field : ACore parameters 3) (angle : ℝ) (point : ClosedDisk) : Matrix (Fin 3) (Fin 3) ℂ :=
  physicalGaugeMatrix (physicalSeedMatrix rho alpha delta parameter angle)
    (((L : ℂ)⁻¹) • operatorMatrix (deriv (harmonicSeedOperator rho alpha delta parameter) angle))
    (originalPhysicalFrameMatrix parameters L epsilon field angle point)⁻¹.transpose point

theorem originalGaugeDeviation_matrix (parameters : PhaseParameters) (L rho alpha delta parameter epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (originalGaugeDeviation parameters L rho alpha delta parameter epsilon field) grade angle point =
      originalPhysicalGaugeMatrix parameters L rho alpha delta parameter epsilon field angle point - 1 := by
  have seedCoherent : FamilyCoherent (seedMatrixFamily (unitDiskAdmissible parameters) rho alpha delta parameter) :=
    (identityFamily_coherent 1 parameters.sigma0 parameters.gamma 1 2).add
      (seedDeviationFamily_coherent (unitDiskAdmissible parameters) rho alpha delta parameter)
  have inverseCoherent := originalInverseFamily_coherent parameters L epsilon field
    (originalCoefficient_low_margin parameters L rho epsilon field low).2.2
  unfold originalGaugeDeviation
  rw [familyMatrix_sub (unitDiskAdmissible parameters) _ _
    (originalGauge_coherent parameters L rho alpha delta parameter epsilon field low) (referenceGauge_coherent parameters)]
  change familyMatrix (originalGauge parameters L rho alpha delta parameter epsilon field) grade angle point -
    familyMatrix (referenceGauge parameters) grade angle point = _
  rw [show familyMatrix (referenceGauge parameters) grade angle point = 1 from
    gaugeFamily_circle (unitDiskAdmissible parameters) grade angle point]
  unfold originalGauge
  rw [gaugeFamily_matrix (unitDiskAdmissible parameters) _ _ _ seedCoherent
    (originalSeedDerivative_coherent parameters L rho alpha delta parameter) inverseCoherent,
    seedMatrixFamily_matrix, originalSeedDerivative_matrix,
    originalInverseFamily_eq_matrixInverse parameters L rho epsilon field low]
  rfl

end Grad.ActualGaugeSigmaPrimitives
