import AKQ13SameWidthAxisCoefficientFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.NonlinearDivision

def axisFrozenProfile (profile : EstimateProfile) : EstimateProfile :=
  ⟨fun grade => Fintype.card (DerivativeIndex grade) * profile.fixed grade,
    fun grade => Fintype.card (DerivativeIndex grade) * profile.deviation grade⟩

theorem axisFrozenFamily_estimate {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {offset input output : ℕ} {profile : EstimateProfile}
    {actual reference : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output}
    (estimate : FamilyEstimate parameters field rho epsilon offset profile actual reference) :
    FamilyEstimate parameters field rho epsilon offset (axisFrozenProfile profile)
      (axisFrozenFamily actual) (axisFrozenFamily reference) where
  actualCoherent := axisFrozenFamily_coherent (unitDiskAdmissible parameters) _ estimate.actualCoherent
  referenceCoherent := axisFrozenFamily_coherent (unitDiskAdmissible parameters) _ estimate.referenceCoherent
  fixedNonnegative grade := mul_nonneg (Nat.cast_nonneg _) (estimate.fixedNonnegative grade)
  deviationNonnegative grade := mul_nonneg (Nat.cast_nonneg _) (estimate.deviationNonnegative grade)
  referenceBound grade := axisFrozenFamily_bound (unitDiskAdmissible parameters) reference _ estimate.referenceBound grade
  deviationBound grade := by
    change ‖axisFrozenCoefficientMap (unitDiskAdmissible parameters) grade input output (actual grade) -
      axisFrozenCoefficientMap (unitDiskAdmissible parameters) grade input output (reference grade)‖ ≤ _
    rw [← map_sub]
    exact (axisFrozenCoefficient_norm_le (unitDiskAdmissible parameters) _).trans
      ((mul_le_mul_of_nonneg_left (estimate.deviationBound grade) (Nat.cast_nonneg _)).trans_eq (mul_assoc _ _ _).symm)

def firstTwoProjection : Matrix (Fin 2) (Fin 3) ℂ := !![1,0,0;0,1,0]
def firstTwoInclusion : Matrix (Fin 3) (Fin 2) ℂ := firstTwoProjection.transpose

def inversePlanarGramFamily {sigma gamma : ℝ} (admissible : Admissible 1 sigma gamma 1)
    (inverse : CoefficientFamily 1 sigma gamma 1 3 3) : CoefficientFamily 1 sigma gamma 1 2 2 :=
  composeFamily admissible (constantFamily 1 sigma gamma 1 (matrixOperator firstTwoProjection))
    (composeFamily admissible (composeFamily admissible inverse (transposeFamily admissible inverse))
      (constantFamily 1 sigma gamma 1 (matrixOperator firstTwoInclusion)))

def inversePlanarGramProfile (profile : EstimateProfile) : EstimateProfile :=
  (constantProfile (matrixOperator firstTwoProjection)).comp 4
    ((profile.comp 4 (transposeProfile 4 3 3 profile)).comp 4
      (constantProfile (matrixOperator firstTwoInclusion)))

theorem inversePlanarGramFamily_estimate {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {profile : EstimateProfile}
    {actual reference : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3}
    (low : physicalBudget parameters field rho epsilon 4 ≤ 1)
    (estimate : FamilyEstimate parameters field rho epsilon 4 profile actual reference) :
    FamilyEstimate parameters field rho epsilon 4 (inversePlanarGramProfile profile)
      (inversePlanarGramFamily (unitDiskAdmissible parameters) actual)
      (inversePlanarGramFamily (unitDiskAdmissible parameters) reference) :=
  FamilyEstimate.comp (unitDiskAdmissible parameters) low
    (constantFamily_estimate parameters (unitDiskAdmissible parameters) field rho epsilon 4 (matrixOperator firstTwoProjection))
    (FamilyEstimate.comp (unitDiskAdmissible parameters) low
      (FamilyEstimate.comp (unitDiskAdmissible parameters) low estimate
        (transposeFamily_estimate (unitDiskAdmissible parameters) low estimate))
      (constantFamily_estimate parameters (unitDiskAdmissible parameters) field rho epsilon 4 (matrixOperator firstTwoInclusion)))

def originalAxisGramFamily (parameters : PhaseParameters) (length epsilon : ℝ) (field : ACore parameters 3) :
    CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 2 2 :=
  axisFrozenFamily (inversePlanarGramFamily (unitDiskAdmissible parameters)
    (originalInverseFamily parameters length epsilon field))

def originalAxisGramReference (parameters : PhaseParameters) : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 2 2 :=
  axisFrozenFamily (inversePlanarGramFamily (unitDiskAdmissible parameters)
    (constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceFrame))

def originalAxisGramProfile (parameters : PhaseParameters) (length : ℝ) : EstimateProfile :=
  axisFrozenProfile (inversePlanarGramProfile (originalInverseProfile parameters length))

/-- Actual K0 circle coefficient, controlled by one original B_(q+4)
on the accepted single low ball and at exactly the original analytic width. -/
theorem originalAxisGramFamily_estimate (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length) :
    FamilyEstimate parameters field rho epsilon 4 (originalAxisGramProfile parameters length)
      (originalAxisGramFamily parameters length epsilon field) (originalAxisGramReference parameters) :=
  axisFrozenFamily_estimate (inversePlanarGramFamily_estimate
    (originalCoefficient_low_margin parameters length rho epsilon field low).2.1
    (originalInverseFamily_estimate parameters length rho epsilon field low))

end Grad.FinitePhysicalJetLift
