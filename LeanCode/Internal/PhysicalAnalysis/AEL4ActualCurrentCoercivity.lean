import AEL3CoerciveDualConstruction
import AIA14ActualCircleReferenceIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularCurrentInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularCurrentEnergy Grad.AnnularTiltedReference Grad.AnnularCircularForm

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

include small

/-- BF12 for the actual full current form, with the original physical outer
term and analytic width. The constant and primitive ball are independent of ell. -/
theorem currentHighFormValue_coercive
    (field : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
    (1 / 32 : ℝ) * ‖field‖ ^ 2 ≤
      (currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field.val field.val).re := by
  have difference := (actualHighForm_onePhysicalBall parameters L compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small).2 field.val field.val
  have exactCircle := circularHighBulkFormValue_eq_reference parameters lower L positive
    (lowerHalf.trans_lt (by norm_num)) lengthPositive widthHalf widthLength field.val field.val field.property
  rw [exactCircle] at difference
  have realDifference := (Complex.abs_re_le_norm
    (currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field.val field.val -
      annularTiltFormValue parameters lower L positive lengthPositive widthHalf widthLength field.val field.val)).trans difference
  have lowerDifference := (abs_le.mp realDifference).1
  have reference := annularTiltForm_coercive_bound parameters lower L positive lengthPositive widthHalf widthLength field.val
  rw [annularTiltForm_literal] at reference
  simp only [Complex.sub_re] at lowerDifference
  change (1 / 32 : ℝ) * ‖field.val‖ ^ 2 ≤ _
  nlinarith only [lowerDifference, reference]

theorem currentHighZeroForm_coercive_bound
    (field : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
    (1 / 32 : ℝ) * ‖field‖ ^ 2 ≤
      currentHighZeroForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field field := by
  rw [currentHighZeroForm_literal]
  exact currentHighFormValue_coercive parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small field

theorem currentHighZeroForm_isCoercive :
    IsCoercive (currentHighZeroForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state) := by
  refine ⟨1 / 32, by norm_num, fun field => ?_⟩
  simpa only [sq, mul_assoc] using currentHighZeroForm_coercive_bound parameters L compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small field

/-- The same inequality in the literal decoded b-weighted BF norm. -/
theorem currentHighFormValue_BF12
    (field : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
    (1 / 32 : ℝ) * (∑' mode : HighAnnularMode, (Grad.CircularHighWeak.highMultiplier mode.val.1)⁻¹ *
      ‖(bEnergyDecode lower L positive field.val).val mode‖ ^ 2) ≤
      (currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field.val field.val).re := by
  rw [← bEnergyDecode_norm_sq]
  exact currentHighFormValue_coercive parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small field

/-- Uniform continuity on the original zero-inner TEST space, also when the
field has nonzero incoming trace. This controls the genuine incoming lift. -/
theorem currentHighFormValue_zeroTest_bound
    (field : annularEnergySpace lower L positive)
    (test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
    ‖currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test.val‖ ≤
      5 * ‖field‖ * ‖test‖ := by
  have difference := (actualHighForm_onePhysicalBall parameters L compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small).2 field test.val
  have exactCircle := circularHighBulkFormValue_eq_reference parameters lower L positive
    (lowerHalf.trans_lt (by norm_num)) lengthPositive widthHalf widthLength field test.val test.property
  rw [exactCircle] at difference
  have reference := annularTiltFormValue_bound parameters lower L positive lengthPositive widthHalf widthLength field test.val
  have triangle := norm_add_le
    (currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test.val -
      annularTiltFormValue parameters lower L positive lengthPositive widthHalf widthLength field test.val)
    (annularTiltFormValue parameters lower L positive lengthPositive widthHalf widthLength field test.val)
  rw [sub_add_cancel] at triangle
  change ‖currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test.val‖ ≤
    5 * ‖field‖ * ‖test.val‖
  nlinarith only [difference, reference, triangle, mul_nonneg (norm_nonneg field) (norm_nonneg test.val)]

end Grad.AnnularCurrentInverse
