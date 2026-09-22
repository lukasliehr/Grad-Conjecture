import AKU74OriginalFiniteAxisLiftPayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.GaugeCoefficients.Physical.Allocation
open Grad.ExhaustionSourceAllocation

theorem localizedQuadraticVectorAxisCore_bound (parameters : PhaseParameters) (dimension grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters dimension) (bound : ℝ),
      (∀ index, ‖Grad.AxisCore.axisEta parameters dimension grade (data index)‖ ≤ bound) →
      originalGradeNorm grade (localizedQuadraticVectorAxisCore data) ≤ constant*bound := by
  choose constants nonnegative bounds using fun index : Fin 3 =>
    vectorAxisProfileCore_bound (parameters := parameters)
      ((localizedFiniteJetLinear dimension).comp (quadraticVectorMonomial dimension index)) grade
  refine ⟨∑ index, constants index, Finset.sum_nonneg (fun index _ => nonnegative index),fun data bound controlled => ?_⟩
  unfold localizedQuadraticVectorAxisCore
  apply (originalGradeNorm_sum_le grade _ _).trans
  calc
    _ ≤ ∑ index, constants index*bound := by
      apply Finset.sum_le_sum
      intro index _
      exact (bounds index (data index)).trans (mul_le_mul_of_nonneg_left (controlled index) (nonnegative index))
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem localizedCubicScalarAxisCore_bound (parameters : PhaseParameters) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (data : Fin 4 → Grad.AxisCore.AxisSmoothCore parameters 1) (bound : ℝ),
      (∀ index, ‖Grad.AxisCore.axisEta parameters 1 grade (data index)‖ ≤ bound) →
      originalGradeNorm grade (localizedCubicScalarAxisCore data) ≤ constant*bound := by
  choose constants nonnegative bounds using fun index : Fin 4 =>
    fixedAxisJetCore_bound (parameters := parameters)
      (localizedFiniteJet (cubicScalarJet (Pi.single index 1))) grade
  refine ⟨∑ index, constants index, Finset.sum_nonneg (fun index _ => nonnegative index),fun data bound controlled => ?_⟩
  unfold localizedCubicScalarAxisCore
  apply (originalGradeNorm_sum_le grade _ _).trans
  calc
    _ ≤ ∑ index, constants index*bound := by
      apply Finset.sum_le_sum
      intro index _
      exact (bounds index (data index)).trans (mul_le_mul_of_nonneg_left (controlled index) (nonnegative index))
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The two literal original smooth core norms, with no change of analytic width. -/
def originalFiniteLiftNorm (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (grade : ℕ) : ℝ :=
  originalGradeNorm grade (originalFiniteLiftU parameters length rho epsilon field low source) +
  originalGradeNorm grade (originalFiniteLiftS parameters length rho epsilon field low source)

/-- The constant precedes the current state and the source. The same finite lift
has one high current factor multiplying only the fixed low source norm. -/
theorem originalFiniteLiftNorm_payment (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (rho epsilon : ℝ) (field : ACore parameters 3)
      (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
      (source : SmoothQuotient parameters),
      originalFiniteLiftNorm parameters length rho epsilon field low source grade ≤
        constant * finiteLiftAxisPayment parameters field rho epsilon source grade := by
  obtain ⟨vectorConstant,vectorNonnegative,vectorBound⟩ := localizedQuadraticVectorAxisCore_bound parameters 3 grade
  obtain ⟨scalarConstant,scalarNonnegative,scalarBound⟩ := localizedQuadraticVectorAxisCore_bound parameters 1 grade
  obtain ⟨cubicConstant,cubicNonnegative,cubicBound⟩ := localizedCubicScalarAxisCore_bound parameters grade
  refine ⟨vectorConstant*|finitePhysicalULiftBound parameters length grade| +
    scalarConstant*(6*diskSupConstant) + cubicConstant*|finiteS3LiftBound parameters length grade|,
    add_nonneg (add_nonneg (mul_nonneg vectorNonnegative (abs_nonneg _))
      (mul_nonneg scalarNonnegative (mul_nonneg (by norm_num) diskSupConstant_pos.le)))
      (mul_nonneg cubicNonnegative (abs_nonneg _)),fun rho epsilon field low source => ?_⟩
  have paymentNonnegative := finiteLiftAxisPayment_nonnegative parameters field rho epsilon source grade
  have vector := vectorBound (originalLiftPhysicalUAxis parameters length rho epsilon field low source)
    (|finitePhysicalULiftBound parameters length grade| * finiteLiftAxisPayment parameters field rho epsilon source grade)
    (fun index => (originalLiftPhysicalUAxis_payment parameters length rho epsilon field low source grade index).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) paymentNonnegative))
  have scalar := scalarBound (originalScalarHessianAxis source)
    ((6*diskSupConstant)*finiteLiftAxisPayment parameters field rho epsilon source grade)
    (fun index => (originalScalarHessianAxis_bound parameters source index grade).trans
      (mul_le_mul_of_nonneg_left ((originalSourceNorm_monotone parameters source (by omega : grade+3 ≤ grade+4)).trans
        (finiteLiftAxisPayment_source_le parameters field rho epsilon source grade))
        (mul_nonneg (by norm_num) diskSupConstant_pos.le)))
  have cubic := cubicBound (originalLiftS3Axis parameters length rho epsilon field low source)
    (|finiteS3LiftBound parameters length grade| * finiteLiftAxisPayment parameters field rho epsilon source grade)
    (fun index => (originalLiftS3Axis_payment parameters length rho epsilon field low source grade index).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) paymentNonnegative))
  unfold originalFiniteLiftNorm originalFiniteLiftU
  rw [originalFiniteLiftS_polynomial]
  exact (add_le_add vector ((Grad.NonlinearQuotientBounds.originalGradeNorm_add_le grade _ _).trans
    (add_le_add scalar cubic))).trans_eq (by ring)

end Grad.FinitePhysicalJetLift
