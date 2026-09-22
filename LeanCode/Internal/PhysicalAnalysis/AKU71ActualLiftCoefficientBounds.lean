import AKU68SharpAxisCoefficientPayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Grad.FinitePhysicalJetLift
open Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Frame

def axisProfileBound (profile : EstimateProfile) (grade : ℕ) : ℝ := profile.fixed grade+profile.deviation grade

def originalMetricAxisBound (parameters : PhaseParameters) (length : ℝ) : ℕ → ℝ :=
  axisProfileBound (axisFrozenProfile (firstTwoInverseGramProfile (originalInverseProfile parameters length)))

def originalDeterminantAxisBound (parameters : PhaseParameters) (length : ℝ) : ℕ → ℝ :=
  axisProfileBound (axisFrozenProfile (determinantProfile (originalInverseProfile parameters length)))

def originalInverseTransposeAxisBound (parameters : PhaseParameters) (length : ℝ) : ℕ → ℝ :=
  axisProfileBound (axisFrozenProfile (transposeProfile 4 3 3 (originalInverseProfile parameters length)))

def originalCubicInverseAxisBound (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) : ℝ :=
  fixedFamilyConstant referenceCubicInverse grade+originalCubicInverseConstant parameters length grade

theorem originalLiftAxis_low_four (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length) :
    physicalBudget parameters field rho epsilon 4 ≤ 1 :=
  (originalCoefficient_low_margin parameters length rho epsilon field
    (originalCubic_low_margin parameters length rho epsilon field low).1).2.1

theorem originalMetricAxisBound_nonnegative (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length) (grade : ℕ) :
    0 ≤ originalMetricAxisBound parameters length grade := by
  have estimate := originalAxisMetricRowsFamily_estimate parameters length rho epsilon field
    (originalCubic_low_margin parameters length rho epsilon field low).1
  exact add_nonneg (estimate.fixedNonnegative grade) (estimate.deviationNonnegative grade)

theorem originalMetricAxisFamily_bound (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length) (grade : ℕ) :
    ‖originalAxisMetricRowsFamily parameters length epsilon field grade‖ ≤
      originalMetricAxisBound parameters length grade * (1+physicalBudget parameters field rho epsilon (grade+4)) :=
  familyEstimate_norm_one_high (originalAxisMetricRowsFamily_estimate parameters length rho epsilon field
    (originalCubic_low_margin parameters length rho epsilon field low).1) grade

theorem originalDeterminantAxisBound_nonnegative (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length) (grade : ℕ) :
    0 ≤ originalDeterminantAxisBound parameters length grade := by
  have estimate := originalAxisInverseDeterminantFamily_estimate parameters length rho epsilon field
    (originalCubic_low_margin parameters length rho epsilon field low).1
  exact add_nonneg (estimate.fixedNonnegative grade) (estimate.deviationNonnegative grade)

theorem originalDeterminantAxisFamily_bound (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length) (grade : ℕ) :
    ‖originalAxisInverseDeterminantFamily parameters length epsilon field grade‖ ≤
      originalDeterminantAxisBound parameters length grade * (1+physicalBudget parameters field rho epsilon (grade+4)) :=
  familyEstimate_norm_one_high (originalAxisInverseDeterminantFamily_estimate parameters length rho epsilon field
    (originalCubic_low_margin parameters length rho epsilon field low).1) grade

theorem originalInverseTransposeAxisBound_nonnegative (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length) (grade : ℕ) :
    0 ≤ originalInverseTransposeAxisBound parameters length grade := by
  have estimate := originalAxisInverseTransposeFamily_estimate parameters length rho epsilon field
    (originalCubic_low_margin parameters length rho epsilon field low).1
  exact add_nonneg (estimate.fixedNonnegative grade) (estimate.deviationNonnegative grade)

theorem originalInverseTransposeAxisFamily_bound (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length) (grade : ℕ) :
    ‖originalAxisInverseTransposeFamily parameters length epsilon field grade‖ ≤
      originalInverseTransposeAxisBound parameters length grade * (1+physicalBudget parameters field rho epsilon (grade+4)) :=
  familyEstimate_norm_one_high (originalAxisInverseTransposeFamily_estimate parameters length rho epsilon field
    (originalCubic_low_margin parameters length rho epsilon field low).1) grade

theorem originalCubicInverseAxisBound_nonnegative (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) :
    0 ≤ originalCubicInverseAxisBound parameters length grade :=
  add_nonneg (fixedFamilyConstant_nonnegative _ _) (originalCubicInverseConstant_nonnegative parameters length grade)

theorem originalCubicInverseAxisFamily_bound (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length) (grade : ℕ) :
    ‖originalCubicInverseFamily parameters length epsilon field grade‖ ≤
      originalCubicInverseAxisBound parameters length grade * (1+physicalBudget parameters field rho epsilon (grade+4)) := by
  have triangle := (norm_le_norm_sub_add (originalCubicInverseFamily parameters length epsilon field grade)
    (constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceCubicInverse grade)).trans
    (add_le_add (originalCubicInverseFamily_one_high parameters length rho epsilon field low grade)
      (constantFamily_norm_le (unitDiskAdmissible parameters) referenceCubicInverse grade))
  have budget := physicalBudget_nonnegative parameters field rho epsilon (grade+4)
  have extra := mul_nonneg (fixedFamilyConstant_nonnegative referenceCubicInverse grade) budget
  rw [Nat.add_comm 4 grade] at triangle
  unfold originalCubicInverseAxisBound
  nlinarith only [triangle,extra,originalCubicInverseConstant_nonnegative parameters length grade]

end Grad.FinitePhysicalJetLift
