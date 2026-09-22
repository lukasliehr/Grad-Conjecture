import AKU19AxisFiniteValueMaps

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger Grad.NonlinearDivision

/-- First two rows of the actual full inverse Gram, retaining its axial
column and hence both original tilt couplings. -/
def firstTwoInverseGramFamily {sigma gamma : ℝ} (admissible : Admissible 1 sigma gamma 1)
    (inverse : CoefficientFamily 1 sigma gamma 1 3 3) : CoefficientFamily 1 sigma gamma 1 3 2 :=
  composeFamily admissible (constantFamily 1 sigma gamma 1 (matrixOperator firstTwoProjection))
    (composeFamily admissible inverse (transposeFamily admissible inverse))

def firstTwoInverseGramProfile (profile : EstimateProfile) : EstimateProfile :=
  (constantProfile (matrixOperator firstTwoProjection)).comp 4
    (profile.comp 4 (transposeProfile 4 3 3 profile))

theorem firstTwoInverseGramFamily_estimate {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {profile : EstimateProfile}
    {actual reference : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3}
    (low : physicalBudget parameters field rho epsilon 4 ≤ 1)
    (estimate : FamilyEstimate parameters field rho epsilon 4 profile actual reference) :
    FamilyEstimate parameters field rho epsilon 4 (firstTwoInverseGramProfile profile)
      (firstTwoInverseGramFamily (unitDiskAdmissible parameters) actual)
      (firstTwoInverseGramFamily (unitDiskAdmissible parameters) reference) :=
  FamilyEstimate.comp (unitDiskAdmissible parameters) low
    (constantFamily_estimate parameters (unitDiskAdmissible parameters) field rho epsilon 4 (matrixOperator firstTwoProjection))
    (FamilyEstimate.comp (unitDiskAdmissible parameters) low estimate
      (transposeFamily_estimate (unitDiskAdmissible parameters) low estimate))

def originalAxisMetricRowsFamily (parameters : PhaseParameters) (length epsilon : ℝ) (field : ACore parameters 3) :
    CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 2 :=
  axisFrozenFamily (firstTwoInverseGramFamily (unitDiskAdmissible parameters)
    (originalInverseFamily parameters length epsilon field))

def originalAxisMetricRowsReference (parameters : PhaseParameters) :
    CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 2 :=
  axisFrozenFamily (firstTwoInverseGramFamily (unitDiskAdmissible parameters)
    (constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceFrame))

theorem originalAxisMetricRowsFamily_estimate (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length) :
    FamilyEstimate parameters field rho epsilon 4
      (axisFrozenProfile (firstTwoInverseGramProfile (originalInverseProfile parameters length)))
      (originalAxisMetricRowsFamily parameters length epsilon field) (originalAxisMetricRowsReference parameters) :=
  axisFrozenFamily_estimate (firstTwoInverseGramFamily_estimate
    (originalCoefficient_low_margin parameters length rho epsilon field low).2.1
    (originalInverseFamily_estimate parameters length rho epsilon field low))

/-- The actual inverse determinant carries the original minus sign:
det(F^-1)=-1/det(A0) at the axis. -/
def originalAxisInverseDeterminantFamily (parameters : PhaseParameters) (length epsilon : ℝ) (field : ACore parameters 3) :
    CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 1 1 :=
  axisFrozenFamily (determinantFamily (unitDiskAdmissible parameters)
    (originalInverseFamily parameters length epsilon field))

def originalAxisInverseDeterminantReference (parameters : PhaseParameters) :
    CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 1 1 :=
  axisFrozenFamily (determinantFamily (unitDiskAdmissible parameters)
    (constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceFrame))

theorem originalAxisInverseDeterminantFamily_estimate (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length) :
    FamilyEstimate parameters field rho epsilon 4
      (axisFrozenProfile (determinantProfile (originalInverseProfile parameters length)))
      (originalAxisInverseDeterminantFamily parameters length epsilon field)
      (originalAxisInverseDeterminantReference parameters) :=
  axisFrozenFamily_estimate (determinantFamily_estimate (unitDiskAdmissible parameters)
    (originalCoefficient_low_margin parameters length rho epsilon field low).2.1
    (originalInverseFamily_estimate parameters length rho epsilon field low))

/-- Reconstruct U2 from the complete covector (u2,c2) with the literal
full F^-T, so the physical toroidal component and tilt are retained. -/
def originalAxisInverseTransposeFamily (parameters : PhaseParameters) (length epsilon : ℝ) (field : ACore parameters 3) :
    CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3 :=
  axisFrozenFamily (transposeFamily (unitDiskAdmissible parameters)
    (originalInverseFamily parameters length epsilon field))

theorem originalAxisInverseTransposeFamily_estimate (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length) :
    FamilyEstimate parameters field rho epsilon 4
      (axisFrozenProfile (transposeProfile 4 3 3 (originalInverseProfile parameters length)))
      (originalAxisInverseTransposeFamily parameters length epsilon field)
      (axisFrozenFamily (transposeFamily (unitDiskAdmissible parameters)
        (constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceFrame))) :=
  axisFrozenFamily_estimate (transposeFamily_estimate (unitDiskAdmissible parameters)
    (originalCoefficient_low_margin parameters length rho epsilon field low).2.1
    (originalInverseFamily_estimate parameters length rho epsilon field low))

end Grad.FinitePhysicalJetLift
