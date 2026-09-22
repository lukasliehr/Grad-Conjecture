import AKN12SameCompletedSourceRows

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarFullSource
open Grad.SourceCollarRestriction Grad.AnnularCurrentSource

theorem actualTiltedRadial_bound {lower : ℝ} (positive : 0 < lower) (bounded : lower ≤ 1) (power : ℕ)
    (weighted original : DivisionRow 2 lower)
    (same : RadialScaleRelated lower (fun radius => ((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ)) weighted original) :
    ‖divisionHighWeight lower positive bounded (radialRowContraction lower positive power original)‖ ≤
      2 * 2 ^ power * ‖weighted‖ := by
  rw [← (same.radial positive power).eq_actualHighWeight positive bounded]
  exact radialRowContraction_bound lower positive power weighted

theorem actualTiltedTangential_bound {lower : ℝ} (positive : 0 < lower) (bounded : lower ≤ 1) (power : ℕ)
    (weighted original : DivisionRow 2 lower)
    (same : RadialScaleRelated lower (fun radius => ((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ)) weighted original) :
    ‖divisionHighWeight lower positive bounded (tangentialRowContraction lower positive power original)‖ ≤
      2 * 2 ^ power * ‖weighted‖ := by
  rw [← (same.tangential positive power).eq_actualHighWeight positive bounded]
  exact tangentialRowContraction_bound lower positive power weighted

theorem originalTiltedRestriction_bound {grade depth power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters 1)
    (flat : ∀ cell, VanishingJets depth (field.val cell)) (paid : depth + power + 2 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (vanishing : 2 ≤ depth) :
    ‖divisionHighWeight lower positive bounded
      (completedRestrictionRow (power := power) (radial := 0) lower positive bounded parameters (by omega)
        (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field)))‖ ≤
      Real.sqrt (remainderAngularBoundConstant depth power 0) * ‖GradeCore.ofCoreLinear (grade := grade) field‖ := by
  rw [← (sourceTiltRow_sameRestriction parameters field flat paid lower positive bounded vanishing).eq_actualHighWeight positive bounded]
  exact sourceTiltRow_bound parameters field flat paid lower positive bounded 0 (by omega)

theorem originalTiltedDivision_bound {grade depth power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters 1)
    (flat : ∀ cell, VanishingJets depth (field.val cell)) (paid : depth + power + 2 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (vanishing : 3 ≤ depth) :
    ‖divisionHighWeight lower positive bounded
      (completedDivisionRow (power := power) (radial := 0) lower positive bounded parameters (by omega)
        (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field)))‖ ≤
      Real.sqrt (remainderAngularBoundConstant depth power 0) * ‖GradeCore.ofCoreLinear (grade := grade) field‖ := by
  rw [← (sourceTiltRow_sameDivision parameters field flat paid lower positive bounded vanishing).eq_actualHighWeight positive bounded]
  exact sourceTiltRow_bound parameters field flat paid lower positive bounded 1 (by omega)

theorem originalTiltedDividedRadial_bound {grade depth power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters 2)
    (flat : ∀ cell, VanishingJets depth (field.val cell)) (paid : depth + power + 2 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (vanishing : 3 ≤ depth) :
    ‖divisionHighWeight lower positive bounded (radialRowContraction lower positive power
      (completedDivisionRow (power := power) (radial := 0) lower positive bounded parameters (by omega)
        (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field))))‖ ≤
      (2 * 2 ^ power * Real.sqrt (remainderAngularBoundConstant depth power 0)) *
        ‖GradeCore.ofCoreLinear (grade := grade) field‖ := by
  have frame := actualTiltedRadial_bound positive bounded power _ _
    (sourceTiltRow_sameDivision parameters field flat paid lower positive bounded vanishing)
  exact frame.trans ((mul_le_mul_of_nonneg_left
    (sourceTiltRow_bound parameters field flat paid lower positive bounded 1 (by omega)) (by positivity)).trans_eq (by ring))

theorem originalTiltedDividedTangential_bound {grade depth power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters 2)
    (flat : ∀ cell, VanishingJets depth (field.val cell)) (paid : depth + power + 2 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (vanishing : 3 ≤ depth) :
    ‖divisionHighWeight lower positive bounded (tangentialRowContraction lower positive power
      (completedDivisionRow (power := power) (radial := 0) lower positive bounded parameters (by omega)
        (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field))))‖ ≤
      (2 * 2 ^ power * Real.sqrt (remainderAngularBoundConstant depth power 0)) *
        ‖GradeCore.ofCoreLinear (grade := grade) field‖ := by
  have frame := actualTiltedTangential_bound positive bounded power _ _
    (sourceTiltRow_sameDivision parameters field flat paid lower positive bounded vanishing)
  exact frame.trans ((mul_le_mul_of_nonneg_left
    (sourceTiltRow_bound parameters field flat paid lower positive bounded 1 (by omega)) (by positivity)).trans_eq (by ring))

end Grad.ExhaustionSourceAllocation
