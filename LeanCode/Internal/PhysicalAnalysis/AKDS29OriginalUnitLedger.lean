import AKDS28FiniteJetCovariantAbsorption
import GSP2PhysicalGaugeMatrix
import GC17Bounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.SourceCollarCoefficients
open Grad.ActualGaugeSigmaPrimitives Grad.ActualCurrentPrimitives
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.InverseAllocation

/-- The original physical length is retained inside the frame and seed
column families, while the coefficient algebra uses the original unit disk. -/
def originalUnitLedgerData (parameters : PhaseParameters) (length rho alpha delta parameter epsilon : ℝ)
    (field : ACore parameters 3) : LedgerData 1 parameters.sigma0 parameters.gamma 1 :=
  assembleData (unitDiskAdmissible parameters)
    (originalFullFrameFamily parameters length epsilon field)
    (originalInverseFamily parameters length epsilon field)
    (seedMatrixFamily (unitDiskAdmissible parameters) rho alpha delta parameter)
    (actualSeedInverse (unitDiskAdmissible parameters) rho alpha delta parameter)
    (originalSeedDerivative parameters length rho alpha delta parameter)
    (originalRotatedFamily parameters length epsilon field)

theorem originalUnitLedgerData_coherent (parameters : PhaseParameters)
    (length rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6≤originalCoefficientLowRadius parameters length)
    (seedBase : ‖seedInverseInput (unitDiskAdmissible parameters) rho alpha delta parameter 0‖≤1/4) :
    LedgerCoherent (originalUnitLedgerData parameters length rho alpha delta parameter epsilon field) := by
  have margin := originalCoefficient_low_margin parameters length rho epsilon field low
  have frame : FamilyCoherent (originalFullFrameFamily parameters length epsilon field) :=
    (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 referenceFrame).add
      (originalFrameFamily_coherent parameters length epsilon field)
  have inverse := originalInverseFamily_coherent parameters length epsilon field margin.2.2
  have seed : FamilyCoherent (seedMatrixFamily (unitDiskAdmissible parameters) rho alpha delta parameter) :=
    (identityFamily_coherent 1 parameters.sigma0 parameters.gamma 1 2).add
      (seedDeviationFamily_coherent (unitDiskAdmissible parameters) rho alpha delta parameter)
  exact assembleData_coherent (unitDiskAdmissible parameters) _ _ _ _ _ _ frame inverse seed
    (actualSeedInverse_coherent (unitDiskAdmissible parameters) rho alpha delta parameter seedBase)
    (originalSeedDerivative_coherent parameters length rho alpha delta parameter)
    (originalRotatedFamily_coherent parameters length epsilon field)

theorem originalUnitLedgerData_gauge (parameters : PhaseParameters)
    (length rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3) :
    (originalUnitLedgerData parameters length rho alpha delta parameter epsilon field).gaugeDeviation=
      originalGaugeDeviation parameters length rho alpha delta parameter epsilon field := rfl

/-- The SAME unit-disk ledger has the actual original physical gauge,
including its length-dependent seed derivative. -/
theorem originalUnitLedgerData_gauge_matrix (parameters : PhaseParameters)
    (length rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6≤originalCoefficientLowRadius parameters length)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (originalUnitLedgerData parameters length rho alpha delta parameter epsilon field).gaugeDeviation grade angle point=
      originalPhysicalGaugeMatrix parameters length rho alpha delta parameter epsilon field angle point-1 := by
  rw [originalUnitLedgerData_gauge]
  exact originalGaugeDeviation_matrix parameters length rho alpha delta parameter epsilon field low grade angle point

end Grad.OriginalCoreRealization
