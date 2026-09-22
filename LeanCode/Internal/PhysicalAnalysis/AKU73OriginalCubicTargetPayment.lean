import AKU72RemainingFiniteMapBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.GaugeCoefficients.Physical.Allocation
open Grad.SourceCollarCoefficients Grad.GaugeCoefficients.Algebra Grad.ExhaustionSourceAllocation

def finiteActionBound (parameters : PhaseParameters) (coefficient data : ℕ → ℝ) (grade : ℕ) : ℝ :=
  axisCoefficientActionConstant parameters coefficient grade*(data grade+2*data 0)

theorem finiteActionBound_nonnegative (parameters : PhaseParameters) (coefficient data : ℕ → ℝ)
    (coefficientNonnegative : ∀ grade, 0 ≤ coefficient grade) (dataNonnegative : ∀ grade, 0 ≤ data grade) (grade : ℕ) :
    0 ≤ finiteActionBound parameters coefficient data grade :=
  mul_nonneg (axisCoefficientActionConstant_nonnegative parameters coefficient coefficientNonnegative grade)
    (add_nonneg (dataNonnegative grade) (mul_nonneg (by norm_num) (dataNonnegative 0)))

def finiteCovectorSeedBound (length : ℝ) (grade : ℕ) : ℝ :=
  axisCovectorConstant*(20*finiteSourceAxisConstant grade+originalC2AxisBound length grade)

theorem finiteCovectorSeedBound_nonnegative (length : ℝ) (grade : ℕ) : 0 ≤ finiteCovectorSeedBound length grade :=
  mul_nonneg axisCovectorConstant_nonnegative
    (add_nonneg (mul_nonneg (by norm_num) (finiteSourceAxisConstant_nonnegative grade)) (originalC2AxisBound_nonnegative length grade))

def originalCovectorSeedAxis (parameters : PhaseParameters) (length : ℝ) (source : SmoothQuotient parameters) (index : Fin 3) :
    Grad.AxisCore.AxisSmoothCore parameters 3 :=
  axisCovectorTriple (-(quadraticAxisPlanarInverse (originalForce2Axis source) index)) (originalC2Axis length source index)

theorem originalCovectorSeedAxis_payment (parameters : PhaseParameters) (field : ACore parameters 3) (rho epsilon length : ℝ)
    (source : SmoothQuotient parameters) (grade : ℕ) (index : Fin 3) :
    ‖Grad.AxisCore.axisEta parameters 3 grade (originalCovectorSeedAxis parameters length source index)‖ ≤
      finiteCovectorSeedBound length grade * finiteLiftAxisPayment parameters field rho epsilon source grade := by
  have force := quadraticAxisPlanarInverse_bound (originalForce2Axis source) grade
    (finiteSourceAxisConstant grade * finiteLiftAxisPayment parameters field rho epsilon source grade)
    (mul_nonneg (finiteSourceAxisConstant_nonnegative grade) (finiteLiftAxisPayment_nonnegative parameters field rho epsilon source grade))
    (originalForce2Axis_payment parameters field rho epsilon source grade) index
  have toroidal := originalC2Axis_payment parameters field rho epsilon length source grade index
  apply (axisCovectorTriple_bound _ _ grade).trans
  rw [map_neg,norm_neg]
  exact (mul_le_mul_of_nonneg_left (add_le_add force toroidal) axisCovectorConstant_nonnegative).trans_eq (by
    unfold finiteCovectorSeedBound
    ring)

def finiteMetricSeedBound (parameters : PhaseParameters) (length : ℝ) : ℕ → ℝ :=
  finiteActionBound parameters (originalMetricAxisBound parameters length) (finiteCovectorSeedBound length)

def finiteDeterminantSourceBound (parameters : PhaseParameters) (length : ℝ) : ℕ → ℝ :=
  finiteActionBound parameters (originalDeterminantAxisBound parameters length) finiteSourceAxisConstant

def originalMetricSeedAxis (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (index : Fin 3) : Grad.AxisCore.AxisSmoothCore parameters 2 :=
  axisFamilyAction (originalAxisMetricRowsFamily parameters length epsilon field)
    (originalAxisMetricRowsFamily_estimate parameters length rho epsilon field
      (originalCubic_low_margin parameters length rho epsilon field low).1).actualCoherent
    (originalCovectorSeedAxis parameters length source index)

theorem originalMetricSeedAxis_payment (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (index : Fin 3) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters 2 grade (originalMetricSeedAxis parameters length rho epsilon field low source index)‖ ≤
      finiteMetricSeedBound parameters length grade * finiteLiftAxisPayment parameters field rho epsilon source grade :=
  axisFamilyAction_source_payment _ _ (originalMetricAxisBound parameters length) (finiteCovectorSeedBound length)
    (originalMetricAxisBound_nonnegative parameters length rho epsilon field low) (finiteCovectorSeedBound_nonnegative length)
    (originalMetricAxisFamily_bound parameters length rho epsilon field low) (originalLiftAxis_low_four parameters length rho epsilon field low)
    source _ (fun indexGrade => originalCovectorSeedAxis_payment parameters field rho epsilon length source indexGrade index) grade

theorem finiteMetricSeedBound_nonnegative (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length) (grade : ℕ) :
    0 ≤ finiteMetricSeedBound parameters length grade :=
  finiteActionBound_nonnegative parameters _ _ (originalMetricAxisBound_nonnegative parameters length rho epsilon field low)
    (finiteCovectorSeedBound_nonnegative length) grade

def originalDeterminantSourceAxis (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (direction : Fin 2) : Grad.AxisCore.AxisSmoothCore parameters 1 :=
  axisFamilyAction (originalAxisInverseDeterminantFamily parameters length epsilon field)
    (originalAxisInverseDeterminantFamily_estimate parameters length rho epsilon field
      (originalCubic_low_margin parameters length rho epsilon field low).1).actualCoherent (traceFirst direction (source 2))

theorem originalDeterminantSourceAxis_payment (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (direction : Fin 2) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters 1 grade (originalDeterminantSourceAxis parameters length rho epsilon field low source direction)‖ ≤
      finiteDeterminantSourceBound parameters length grade * finiteLiftAxisPayment parameters field rho epsilon source grade :=
  axisFamilyAction_source_payment _ _ (originalDeterminantAxisBound parameters length) finiteSourceAxisConstant
    (originalDeterminantAxisBound_nonnegative parameters length rho epsilon field low) finiteSourceAxisConstant_nonnegative
    (originalDeterminantAxisFamily_bound parameters length rho epsilon field low) (originalLiftAxis_low_four parameters length rho epsilon field low)
    source _ (fun indexGrade => originalScalarFirstAxis_payment parameters field rho epsilon source indexGrade 2 direction) grade

def finiteCubicTargetBound (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) : ℝ :=
  ‖(length : ℂ)⁻¹‖*2*finiteDeterminantSourceBound parameters length grade+6*finiteMetricSeedBound parameters length grade

theorem finiteCubicTargetBound_nonnegative (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length) (grade : ℕ) :
    0 ≤ finiteCubicTargetBound parameters length grade := by
  have determinant := finiteActionBound_nonnegative parameters _ _
    (originalDeterminantAxisBound_nonnegative parameters length rho epsilon field low) finiteSourceAxisConstant_nonnegative grade
  have metric := finiteMetricSeedBound_nonnegative parameters length rho epsilon field low grade
  change 0 ≤ finiteDeterminantSourceBound parameters length grade at determinant
  unfold finiteCubicTargetBound
  positivity

theorem originalCubicTargetAxis_payment (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters 2 grade (originalCubicTargetAxis parameters length rho epsilon field low source)‖ ≤
      finiteCubicTargetBound parameters length grade * finiteLiftAxisPayment parameters field rho epsilon source grade := by
  have determinant := (scalarAxisPair_bound
    (originalDeterminantSourceAxis parameters length rho epsilon field low source 0)
    (originalDeterminantSourceAxis parameters length rho epsilon field low source 1) grade).trans
    (add_le_add (originalDeterminantSourceAxis_payment parameters length rho epsilon field low source 0 grade)
      (originalDeterminantSourceAxis_payment parameters length rho epsilon field low source 1 grade))
  have metric := axisQuadraticDivergence_bound
    (originalMetricSeedAxis parameters length rho epsilon field low source) grade
    (finiteMetricSeedBound parameters length grade * finiteLiftAxisPayment parameters field rho epsilon source grade)
    (fun index => originalMetricSeedAxis_payment parameters length rho epsilon field low source index grade)
  change ‖Grad.AxisCore.axisEta parameters 2 grade ((length : ℂ)⁻¹ •
    scalarAxisPair (originalDeterminantSourceAxis parameters length rho epsilon field low source 0)
      (originalDeterminantSourceAxis parameters length rho epsilon field low source 1) -
    axisQuadraticDivergence (originalMetricSeedAxis parameters length rho epsilon field low source))‖ ≤ _
  rw [map_sub,map_smul]
  have triangle := norm_sub_le ((length : ℂ)⁻¹ • Grad.AxisCore.axisEta parameters 2 grade
    (scalarAxisPair (originalDeterminantSourceAxis parameters length rho epsilon field low source 0)
      (originalDeterminantSourceAxis parameters length rho epsilon field low source 1)))
    (Grad.AxisCore.axisEta parameters 2 grade (axisQuadraticDivergence (originalMetricSeedAxis parameters length rho epsilon field low source)))
  rw [norm_smul] at triangle
  exact triangle.trans ((add_le_add (mul_le_mul_of_nonneg_left determinant (norm_nonneg _)) metric).trans_eq (by
    unfold finiteCubicTargetBound
    ring))

end Grad.FinitePhysicalJetLift
