import GSP15OriginalGaugeSigmaConsumer

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.InverseAllocation Grad.GaugeCoefficients.Physical.Ledger

/-- One original B6 ball for both actual frame and seed inverses, fixed
before all tangential grades. -/
def boundaryCoefficientLowRadius (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  min (originalCoefficientLowRadius parameters L) (ledgerLowRadius parameters 1 compact 1)

theorem boundaryCoefficientLowRadius_positive (parameters : PhaseParameters) (L compact : ℝ) :
    0 < boundaryCoefficientLowRadius parameters L compact :=
  lt_min (originalCoefficientLowRadius_positive parameters L)
    (ledgerLowRadius_positive parameters (by norm_num : (0 : ℝ) < 1) compact (by norm_num))

theorem boundaryCoefficientLowRadius_le_original (parameters : PhaseParameters) (L compact : ℝ) :
    boundaryCoefficientLowRadius parameters L compact ≤ originalCoefficientLowRadius parameters L :=
  min_le_left _ _

theorem boundaryCoefficient_seed_margin (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact) :
    |rho| ≤ 1 ∧ physicalBudget parameters field rho epsilon 4 ≤ 1 ∧
      ‖seedInverseInput (unitDiskAdmissible parameters) rho alpha delta parameter 0‖ ≤ 1 / 4 := by
  have margin := originalCoefficient_low_margin parameters L rho epsilon field
    (low.trans (boundaryCoefficientLowRadius_le_original parameters L compact))
  have rhoSmall : |rho| ≤ 1 := by
    have lowFour := margin.2.1
    unfold physicalBudget at lowFour
    linarith [Grad.NonlinearProduct.originalGradeNorm_nonnegative 4 field, abs_nonneg epsilon]
  refine ⟨rhoSmall, margin.2.1, ?_⟩
  exact (actualInverseInput_margins parameters (unitDiskAdmissible parameters)
    compactNonnegative (by norm_num : (0 : ℝ) < 1) rho alpha delta parameter epsilon
    rhoSmall alphaSmall deltaSmall parameterSmall margin.1 field
    (low.trans (min_le_right _ _))).2.2

/-- Actual original Cartesian boundary covector Y^T M^-1 iota^T F^-T.
At r=1 this is exactly AD19's beta_M^T F^-T. -/
def originalBoundaryFamily (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3) :
    CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 1 :=
  traceFamily (unitDiskAdmissible parameters)
    (actualSeedInverse (unitDiskAdmissible parameters) rho alpha delta parameter)
    (originalInverseFamily parameters L epsilon field)

def referenceBoundaryFamily (parameters : PhaseParameters) :
    CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 1 :=
  traceFamily (unitDiskAdmissible parameters)
    (identityFamily 1 parameters.sigma0 parameters.gamma 1 2)
    (constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceFrame)

def originalBoundaryProfile (parameters : PhaseParameters) (L compact : ℝ) : EstimateProfile :=
  traceProfile (inverseSeedProfile parameters.sigma0 compact) (originalInverseProfile parameters L)

theorem originalBoundaryFamily_estimate (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact) :
    FamilyEstimate parameters field rho epsilon 4 (originalBoundaryProfile parameters L compact)
      (originalBoundaryFamily parameters L rho alpha delta parameter epsilon field)
      (referenceBoundaryFamily parameters) := by
  have margin := boundaryCoefficient_seed_margin parameters L rho alpha delta parameter epsilon compact
    field compactNonnegative alphaSmall deltaSmall parameterSmall low
  exact traceFamily_estimate (unitDiskAdmissible parameters) margin.2.1
    (actualSeedInverse_estimate parameters (unitDiskAdmissible parameters) compactNonnegative
      rho alpha delta parameter epsilon margin.1 alphaSmall deltaSmall parameterSmall field
      margin.2.1 margin.2.2)
    (originalInverseFamily_estimate parameters L rho epsilon field
      (low.trans (boundaryCoefficientLowRadius_le_original parameters L compact)))

end Grad.ActualBoundaryPrimitives
