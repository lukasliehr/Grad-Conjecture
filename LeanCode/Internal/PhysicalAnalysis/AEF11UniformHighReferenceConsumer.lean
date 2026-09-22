import AEF10UniformBoundedTiltInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Grad.AnnularUniformBoundary

open Grad.CartesianState Grad.AnnularVariational Grad.AnnularGrades
open Grad.AnnularTiltedReference Grad.AnnularHighTilt
open Grad.CircularHighWeak Grad.AnnularReconstruction

section Consumer

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- Consumer for the actual uniform incoming lift in literal stored
`b_m⁻¹` coordinates. -/
theorem actualUniformBIncomingLift_consumer (boundary : AnnularBoundary) :
    ‖uniformBInnerLift lower length positive lowerHalf lengthPositive boundary‖ ≤
        2 * uniformInnerLiftConstant length * ‖boundary‖ ∧
    annularEnergyTrace lower length positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive 0 (bEnergyDecode lower length positive
        (uniformBInnerLift lower length positive lowerHalf lengthPositive boundary)) = boundary ∧
    annularEnergyTrace lower length positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive 1 (bEnergyDecode lower length positive
        (uniformBInnerLift lower length positive lowerHalf lengthPositive boundary)) = 0 :=
  ⟨uniformBInnerLift_bound lower length positive lowerHalf lengthPositive boundary,
    uniformBInnerLift_decoded_inner lower length positive lowerHalf lengthPositive boundary,
    uniformBInnerLift_decoded_outer lower length positive lowerHalf lengthPositive boundary⟩

/-- Full-data uniform high reference estimate for the same exact solution as
the accepted physical inverse.  It retains the literal `b_m⁻¹` energy, the
complete weak test space, and all original physical equations. -/
theorem actualUniformBWeightedTiltedReference_consumer
    (data : AnnularForcing lower × AnnularBoundary) :
    let field := annularTiltVariationalUniformInverse parameters lower length positive
      lowerHalf lengthPositive widthHalf widthLength data
    annularEnergyTrace lower length positive (lowerHalf.trans_lt (by norm_num))
        lengthPositive 0 field = data.2 ∧
    (∀ test : annularInnerZero lower length positive
        (lowerHalf.trans_lt (by norm_num)) lengthPositive,
      annularTiltFormValue parameters lower length positive lengthPositive widthHalf widthLength
          field test.val =
        annularTiltFunctionalValue parameters lower length positive
          (lowerHalf.trans_lt (by norm_num)) lengthPositive widthHalf widthLength
          data.1 test.val) ∧
    (∑' mode : HighAnnularMode, (highMultiplier mode.val.1)⁻¹ *
      ‖(bEnergyDecode lower length positive field).val mode‖ ^ 2) ≤
        annularTiltUniformInverseConstant length ^ 2 * ‖data‖ ^ 2 ∧
    (highEnergyUnweight lower length positive (lowerHalf.trans (by norm_num))
        field =
      annularVariationalSolution parameters lower length positive
        (lowerHalf.trans_lt (by norm_num)) lengthPositive widthHalf widthLength
        (highForcingUnweight lower positive (lowerHalf.trans (by norm_num)) data.1)
        (((lower ^ highTiltExponent : ℝ) : ℂ) • data.2) ∧
      ActualAnnularPhysicalLaws parameters lower length positive
        (lowerHalf.trans_lt (by norm_num)) lengthPositive widthHalf widthLength
        (highForcingUnweight lower positive (lowerHalf.trans (by norm_num)) data.1)
        (((lower ^ highTiltExponent : ℝ) : ℂ) • data.2)) := by
  dsimp only
  refine ⟨annularTiltVariationalSolution_inner parameters lower length positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive widthHalf widthLength data.1 data.2,
    annularTiltVariationalSolution_weak parameters lower length positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive widthHalf widthLength data.1 data.2,
    ?_, ?_⟩
  · rw [← bEnergyDecode_norm_sq]
    have bound := pow_le_pow_left₀ (norm_nonneg _)
      (annularTiltVariationalLinear_uniform_bound parameters lower length positive lowerHalf
        lengthPositive widthHalf widthLength data) 2
    change ‖annularTiltVariationalLinear parameters lower length positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive widthHalf widthLength data‖ ^ 2 ≤ _
    simpa only [mul_pow] using bound
  · exact annularTiltReference_physical_consumer parameters lower length positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive widthHalf widthLength data.1 data.2

/-- The decoded outer/inner convention agrees exactly with the already
accepted fixed-collar inverse; only its operator norm proof has changed. -/
theorem actualUniformBWeightedTiltedReference_decoded_inner
    (data : AnnularForcing lower × AnnularBoundary) :
    annularEnergyTrace lower length positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive 0 (bEnergyDecode lower length positive
        (annularTiltVariationalUniformInverse parameters lower length positive lowerHalf
          lengthPositive widthHalf widthLength data)) =
    realLpDiagonal (fun mode : HighAnnularMode => Real.sqrt (highMultiplier mode.val.1))
      1 (by norm_num) bEnergyDecode_bound data.2 := by
  rw [annularTiltVariationalUniformInverse_eq_fixed]
  exact actualBWeightedTiltedReference_decoded_inner parameters lower length positive
    (lowerHalf.trans_lt (by norm_num)) lengthPositive widthHalf widthLength data

end Consumer

end Grad.AnnularUniformBoundary
