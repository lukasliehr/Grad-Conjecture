import ProductWeightedInputs
import ProductSequenceConvolution

noncomputable section

open scoped BigOperators ENNReal

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.CartesianState

def wordGradeIndex {order : ℕ} (word : CartesianWord order) (power : ℕ) :
    GradeMultiIndex (order + power) :=
  (gradeMultiIndexEquiv (order + power)).symm
    ⟨cartesianWordIndex word, by rw [cartesianWordIndex_order]; omega⟩

theorem wordGradeIndex_cartesian {order : ℕ} (word : CartesianWord order) (power : ℕ) :
    (wordGradeIndex word power).toCartesian = cartesianWordIndex word := by
  exact congrArg Subtype.val ((gradeMultiIndexEquiv (order + power)).apply_symm_apply _)

/-- The last input remains in outer l2 and disk L2. No Sobolev grade is spent. -/
def weightedWordL2Sequence {dimension order : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (word : CartesianWord order) (power : ℕ) :
    lp (fun _ : ℤ => ℝ) 2 :=
  ⟨fun cell => ‖ordinaryRawGradeCoordinates (order + power)
      (weightedCoefficientCoreEquiv parameters field).val cell (wordGradeIndex word power)‖, by
    apply ((weightedCoefficientCoreEquiv parameters field).property (order + power)).mono'
    intro cell
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact PiLp.norm_apply_le _ (wordGradeIndex word power)⟩

theorem weightedWordL2Sequence_nonnegative {dimension order : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (word : CartesianWord order) (power : ℕ) (cell : ℤ) :
    0 ≤ weightedWordL2Sequence parameters field word power cell := norm_nonneg _

theorem weightedWordL2Sequence_value {dimension order : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (word : CartesianWord order) (power : ℕ) (cell : ℤ) :
    weightedWordL2Sequence parameters field word power cell = cellFrequency cell ^ power *
      ‖closedContinuousToDiskL2 (closedDerivative
        (phaseWeightedJet parameters cell (field.val cell)) order word)‖ := by
  change ‖(cellFrequency cell : ℂ) ^
      (order + power - cartesianOrder (wordGradeIndex word power).toCartesian) •
      closedContinuousToDiskL2 (closedMultiDerivative
        (phaseWeightedJet parameters cell (field.val cell)) (wordGradeIndex word power).toCartesian)‖ = _
  rw [wordGradeIndex_cartesian, cartesianWordIndex_order,
    Nat.add_sub_cancel_left, norm_smul, Complex.norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (cellFrequency_pos cell).le,
    closedDerivative_eq_closedMultiDerivative_wordIndex]

theorem weightedWordL2Sequence_norm_bound {dimension order : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (word : CartesianWord order) (power : ℕ) :
    ‖weightedWordL2Sequence parameters field word power‖ ≤ originalGradeNorm (order + power) field := by
  rw [← weighted_ordinaryGrade_norm parameters field]
  apply lp.norm_mono (by norm_num)
  intro cell
  change ‖‖ordinaryRawGradeCoordinates (order + power)
      (weightedCoefficientCoreEquiv parameters field).val cell (wordGradeIndex word power)‖‖ ≤ _
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact PiLp.norm_apply_le _ (wordGradeIndex word power)

end Grad.NonlinearProduct
