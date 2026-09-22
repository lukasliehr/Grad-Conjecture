import BCT2PhysicalBoundaryRow

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients
open Grad.ActualGaugeSigmaPrimitives
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.InverseAllocation Grad.GaugeCoefficients.Physical.Ledger

/-- Fixed embedding of the scalar row in the third output coordinate lets
the accepted full polar Fourier calculus act on the actual AD19 row. -/
def paddedBoundaryFamily (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3) :
    CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3 :=
  composeFamily (unitDiskAdmissible parameters)
    (constantFamily 1 parameters.sigma0 parameters.gamma 1 (matrixOperator thirdFrameColumn))
    (originalBoundaryFamily parameters L rho alpha delta parameter epsilon field)

def paddedBoundaryReference (parameters : PhaseParameters) :
    CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3 :=
  composeFamily (unitDiskAdmissible parameters)
    (constantFamily 1 parameters.sigma0 parameters.gamma 1 (matrixOperator thirdFrameColumn))
    (referenceBoundaryFamily parameters)

def paddedBoundaryProfile (parameters : PhaseParameters) (L compact : ℝ) : EstimateProfile :=
  (constantProfile (matrixOperator thirdFrameColumn)).comp 4 (originalBoundaryProfile parameters L compact)

theorem paddedBoundaryFamily_estimate (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact) :
    FamilyEstimate parameters field rho epsilon 4 (paddedBoundaryProfile parameters L compact)
      (paddedBoundaryFamily parameters L rho alpha delta parameter epsilon field)
      (paddedBoundaryReference parameters) := by
  have original := originalBoundaryFamily_estimate parameters L rho alpha delta parameter epsilon compact
    field compactNonnegative alphaSmall deltaSmall parameterSmall low
  have margin := boundaryCoefficient_seed_margin parameters L rho alpha delta parameter epsilon compact
    field compactNonnegative alphaSmall deltaSmall parameterSmall low
  exact FamilyEstimate.comp (unitDiskAdmissible parameters) margin.2.1
    (constantFamily_estimate parameters (unitDiskAdmissible parameters) field rho epsilon 4
      (matrixOperator thirdFrameColumn)) original

def boundaryPolarDeviation (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3) :
    CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3 :=
  fun grade => paddedBoundaryFamily parameters L rho alpha delta parameter epsilon field grade -
    paddedBoundaryReference parameters grade

theorem boundaryPolarDeviation_coherent (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact) :
    FamilyCoherent (boundaryPolarDeviation parameters L rho alpha delta parameter epsilon field) :=
  (paddedBoundaryFamily_estimate parameters L rho alpha delta parameter epsilon compact
    field compactNonnegative alphaSmall deltaSmall parameterSmall low).actualCoherent.sub
    (paddedBoundaryFamily_estimate parameters L rho alpha delta parameter epsilon compact
      field compactNonnegative alphaSmall deltaSmall parameterSmall low).referenceCoherent

theorem boundaryPolarDeviation_bound (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact)
    (grade : ℕ) :
    ‖boundaryPolarDeviation parameters L rho alpha delta parameter epsilon field grade‖ ≤
      (paddedBoundaryProfile parameters L compact).deviation grade *
        physicalBudget parameters field rho epsilon (4 + grade) :=
  (paddedBoundaryFamily_estimate parameters L rho alpha delta parameter epsilon compact
    field compactNonnegative alphaSmall deltaSmall parameterSmall low).deviationBound grade

end Grad.ActualBoundaryPrimitives
