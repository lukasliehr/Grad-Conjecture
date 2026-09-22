import ACP16ForceCoefficientConsumer

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.ActualGaugeSigmaPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger

def originalSeedDerivative (parameters : PhaseParameters) (L rho alpha delta parameter : ℝ) :
    CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 2 2 :=
  fun grade => ((L : ℂ)⁻¹) • seedDerivativeCoefficient (unitDiskAdmissible parameters) grade rho alpha delta parameter

theorem originalSeedDerivative_coherent (parameters : PhaseParameters) (L rho alpha delta parameter : ℝ) :
    FamilyCoherent (originalSeedDerivative parameters L rho alpha delta parameter) :=
  (seedDerivativeFamily_coherent (unitDiskAdmissible parameters) rho alpha delta parameter).smul ((L : ℂ)⁻¹)

def originalGauge (parameters : PhaseParameters) (L rho alpha delta parameter epsilon : ℝ)
    (field : ACore parameters 3) : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3 :=
  gaugeFamily (unitDiskAdmissible parameters)
    (seedMatrixFamily (unitDiskAdmissible parameters) rho alpha delta parameter)
    (originalSeedDerivative parameters L rho alpha delta parameter)
    (originalInverseFamily parameters L epsilon field)

def referenceGauge (parameters : PhaseParameters) : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3 :=
  gaugeFamily (unitDiskAdmissible parameters) (identityFamily 1 parameters.sigma0 parameters.gamma 1 2)
    (zeroFamily 1 parameters.sigma0 parameters.gamma 1 2 2)
    (constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceFrame)

def originalGaugeDeviation (parameters : PhaseParameters) (L rho alpha delta parameter epsilon : ℝ)
    (field : ACore parameters 3) : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3 :=
  fun grade => originalGauge parameters L rho alpha delta parameter epsilon field grade - referenceGauge parameters grade

def originalGaugeProfile (parameters : PhaseParameters) (L radius : ℝ) : EstimateProfile :=
  gaugeProfile (seedMatrixProfile parameters.sigma0 radius)
    ((seedDerivativeProfile parameters.sigma0 radius).smul ((L : ℂ)⁻¹))
    (originalInverseProfile parameters L)

theorem originalGauge_estimate (parameters : PhaseParameters) (L rho alpha delta parameter epsilon radius : ℝ)
    (field : ACore parameters 3) (radiusNonnegative : 0 ≤ radius)
    (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius) (parameterSmall : |parameter| ≤ radius)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L) :
    FamilyEstimate parameters field rho epsilon 4 (originalGaugeProfile parameters L radius)
      (originalGauge parameters L rho alpha delta parameter epsilon field) (referenceGauge parameters) := by
  have margin := originalCoefficient_low_margin parameters L rho epsilon field low
  have rhoSmall : |rho| ≤ 1 := by
    have nonnegative := Grad.NonlinearProduct.originalGradeNorm_nonnegative 4 field
    have bound := margin.2.1
    unfold physicalBudget at bound
    linarith [abs_nonneg epsilon]
  have seedEstimate := seedMatrixFamily_estimate parameters (unitDiskAdmissible parameters) radiusNonnegative
    rho alpha delta parameter epsilon rhoSmall alphaSmall deltaSmall parameterSmall field
  have derivativeEstimate := (seedDerivativeFamily_estimate parameters (unitDiskAdmissible parameters) radiusNonnegative
    rho alpha delta parameter epsilon rhoSmall alphaSmall deltaSmall parameterSmall field).smul ((L : ℂ)⁻¹)
  have derivativeReference : (fun grade => ((L : ℂ)⁻¹) •
      zeroFamily 1 parameters.sigma0 parameters.gamma 1 2 2 grade) =
      zeroFamily 1 parameters.sigma0 parameters.gamma 1 2 2 := by
    funext grade
    exact smul_zero _
  rw [derivativeReference] at derivativeEstimate
  exact gaugeFamily_estimate (unitDiskAdmissible parameters) margin.2.1 seedEstimate derivativeEstimate
    (originalInverseFamily_estimate parameters L rho epsilon field low)

theorem originalGaugeDeviation_coherent (parameters : PhaseParameters) (L rho alpha delta parameter epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L) :
    FamilyCoherent (originalGaugeDeviation parameters L rho alpha delta parameter epsilon field) := by
  have seedCoherent := (identityFamily_coherent 1 parameters.sigma0 parameters.gamma 1 2).add
    (seedDeviationFamily_coherent (unitDiskAdmissible parameters) rho alpha delta parameter)
  exact (gaugeFamily_coherent (unitDiskAdmissible parameters) _ _ _ seedCoherent
    (originalSeedDerivative_coherent parameters L rho alpha delta parameter)
    (originalInverseFamily_coherent parameters L epsilon field
      (originalCoefficient_low_margin parameters L rho epsilon field low).2.2)).sub
    (gaugeFamily_coherent (unitDiskAdmissible parameters) _ _ _
      (identityFamily_coherent 1 parameters.sigma0 parameters.gamma 1 2)
      (zeroFamily_coherent 1 parameters.sigma0 parameters.gamma 1 2 2)
      (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 referenceFrame))

theorem originalGaugeDeviation_bound (parameters : PhaseParameters) (L rho alpha delta parameter epsilon radius : ℝ)
    (field : ACore parameters 3) (radiusNonnegative : 0 ≤ radius)
    (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius) (parameterSmall : |parameter| ≤ radius)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L) (grade : ℕ) :
    ‖originalGaugeDeviation parameters L rho alpha delta parameter epsilon field grade‖ ≤
      (originalGaugeProfile parameters L radius).deviation grade * physicalBudget parameters field rho epsilon (4 + grade) :=
  (originalGauge_estimate parameters L rho alpha delta parameter epsilon radius field radiusNonnegative
    alphaSmall deltaSmall parameterSmall low).deviationBound grade

end Grad.ActualGaugeSigmaPrimitives
