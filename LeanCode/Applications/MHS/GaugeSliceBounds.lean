import GaugeSliceInverse

noncomputable section

set_option maxHeartbeats 3200000

open scoped BigOperators

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers

variable (phase : PhaseParameters)
variable (parameterM : Seed.Parameters) (insideM : parameterM ∈ Seed.parameterDomain)
variable (parameterN : Seed.Parameters) (insideN : parameterN ∈ Seed.parameterDomain)

/-- Grade constant of the poloidal gauge composite. -/
def gaugeCompositeGradeConstant (grade : ℕ) : ℝ :=
  tangentialGradeConstant grade *
    (multiplierConstant grade phase.gamma * envelope phase grade (seedTransposeCells parameterN) *
      (multiplierConstant grade phase.gamma * envelope phase grade (seedMatrixCells parameterN)))

theorem gaugeCompositeGradeConstant_nonneg (grade : ℕ) :
    0 ≤ gaugeCompositeGradeConstant phase parameterN grade := by
  unfold gaugeCompositeGradeConstant
  have first := tangentialGradeConstant_nonnegative grade
  have second := multiplierConstant_nonnegative grade phase.gamma phase.gamma_pos.le
  have third := envelope_nonneg' phase grade (seedTransposeCells parameterN)
  have fourth := envelope_nonneg' phase grade (seedMatrixCells parameterN)
  positivity

theorem gaugeComposite_coordinates_bound {grade : ℕ} (field : ACore phase 2) :
    ‖cartesianGradeCoordinates phase grade
        (gaugeComposite phase parameterN insideN field)‖ ≤
      gaugeCompositeGradeConstant phase parameterN grade *
        ‖cartesianGradeCoordinates phase grade field‖ := by
  rw [gaugeComposite_apply]
  have matrixBound := smoothMultiplier_coordinates_bound (grade := grade) phase
    (seedMatrixCells parameterN) (seedMatrixCells_envelope_summable phase parameterN insideN)
    field
  have transposeBound := smoothMultiplier_coordinates_bound (grade := grade) phase
    (seedTransposeCells parameterN)
    (seedTransposeCells_envelope_summable phase parameterN insideN)
    (seedMatrixCore phase parameterN insideN field)
  have tangentialBound := tangentialCore_coordinates_bound (grade := grade) phase
    (seedTransposeCore phase parameterN insideN (seedMatrixCore phase parameterN insideN field))
  have matrixIdentify := seedMatrixCore_eq_full phase parameterN insideN field
  have multiplierNonneg := multiplierConstant_nonnegative grade phase.gamma phase.gamma_pos.le
  have transposeEnvNonneg := envelope_nonneg' phase grade (seedTransposeCells parameterN)
  have matrixEnvNonneg := envelope_nonneg' phase grade (seedMatrixCells parameterN)
  have tangentialNonneg := tangentialGradeConstant_nonnegative grade
  calc ‖cartesianGradeCoordinates phase grade (tangentialCore phase
        (seedTransposeCore phase parameterN insideN
          (seedMatrixCore phase parameterN insideN field)))‖
      ≤ tangentialGradeConstant grade * ‖cartesianGradeCoordinates phase grade
          (seedTransposeCore phase parameterN insideN
            (seedMatrixCore phase parameterN insideN field))‖ := tangentialBound
    _ ≤ tangentialGradeConstant grade * (multiplierConstant grade phase.gamma *
          envelope phase grade (seedTransposeCells parameterN) *
            ‖cartesianGradeCoordinates phase grade
              (seedMatrixCore phase parameterN insideN field)‖) :=
        mul_le_mul_of_nonneg_left transposeBound tangentialNonneg
    _ ≤ tangentialGradeConstant grade * (multiplierConstant grade phase.gamma *
          envelope phase grade (seedTransposeCells parameterN) *
            (multiplierConstant grade phase.gamma *
              envelope phase grade (seedMatrixCells parameterN) *
                ‖cartesianGradeCoordinates phase grade field‖)) := by
        apply mul_le_mul_of_nonneg_left _ tangentialNonneg
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg multiplierNonneg transposeEnvNonneg)
        rw [matrixIdentify]
        exact matrixBound
    _ = gaugeCompositeGradeConstant phase parameterN grade *
          ‖cartesianGradeCoordinates phase grade field‖ := by
        unfold gaugeCompositeGradeConstant
        ring

/-- Grade constant of the planar transfer. -/
def planarTransferGradeConstant (grade : ℕ) : ℝ :=
  multiplierConstant grade phase.gamma * envelope phase grade (seedMatrixCells parameterN) *
    ((1 + gaugeCompositeGradeConstant phase parameterN grade) *
      (multiplierConstant grade phase.gamma *
        envelope phase grade (seedInverseCells parameterM)))

theorem planarTransferGradeConstant_nonneg (grade : ℕ) :
    0 ≤ planarTransferGradeConstant phase parameterM parameterN grade := by
  unfold planarTransferGradeConstant
  have first := multiplierConstant_nonnegative grade phase.gamma phase.gamma_pos.le
  have second := envelope_nonneg' phase grade (seedMatrixCells parameterN)
  have third := gaugeCompositeGradeConstant_nonneg phase parameterN grade
  have fourth := envelope_nonneg' phase grade (seedInverseCells parameterM)
  positivity

theorem planarTransfer_coordinates_bound {grade : ℕ} (field : ACore phase 2) :
    ‖cartesianGradeCoordinates phase grade
        (planarTransfer phase parameterM insideM parameterN insideN field)‖ ≤
      planarTransferGradeConstant phase parameterM parameterN grade *
        ‖cartesianGradeCoordinates phase grade field‖ := by
  rw [planarTransfer_apply]
  have inverseBound : ‖cartesianGradeCoordinates phase grade
      (seedInverseCore phase parameterM insideM field)‖ ≤
      multiplierConstant grade phase.gamma * envelope phase grade (seedInverseCells parameterM) *
        ‖cartesianGradeCoordinates phase grade field‖ := by
    rw [seedInverseCore_eq_full phase parameterM insideM field]
    exact smoothMultiplier_coordinates_bound (grade := grade) phase _ _ field
  have sliceBound : ‖cartesianGradeCoordinates phase grade
      (sliceProjection phase parameterN insideN
        (seedInverseCore phase parameterM insideM field))‖ ≤
      (1 + gaugeCompositeGradeConstant phase parameterN grade) *
        ‖cartesianGradeCoordinates phase grade
          (seedInverseCore phase parameterM insideM field)‖ := by
    rw [sliceProjection_apply, map_sub]
    calc ‖cartesianGradeCoordinates phase grade
            (seedInverseCore phase parameterM insideM field) -
          cartesianGradeCoordinates phase grade (gaugeComposite phase parameterN insideN
            (seedInverseCore phase parameterM insideM field))‖
        ≤ ‖cartesianGradeCoordinates phase grade
              (seedInverseCore phase parameterM insideM field)‖ +
            ‖cartesianGradeCoordinates phase grade (gaugeComposite phase parameterN insideN
              (seedInverseCore phase parameterM insideM field))‖ := norm_sub_le _ _
      _ ≤ ‖cartesianGradeCoordinates phase grade
              (seedInverseCore phase parameterM insideM field)‖ +
            gaugeCompositeGradeConstant phase parameterN grade *
              ‖cartesianGradeCoordinates phase grade
                (seedInverseCore phase parameterM insideM field)‖ :=
          add_le_add le_rfl (gaugeComposite_coordinates_bound phase parameterN insideN _)
      _ = (1 + gaugeCompositeGradeConstant phase parameterN grade) *
            ‖cartesianGradeCoordinates phase grade
              (seedInverseCore phase parameterM insideM field)‖ := by ring
  have matrixBound : ‖cartesianGradeCoordinates phase grade
      (seedMatrixCore phase parameterN insideN (sliceProjection phase parameterN insideN
        (seedInverseCore phase parameterM insideM field)))‖ ≤
      multiplierConstant grade phase.gamma * envelope phase grade (seedMatrixCells parameterN) *
        ‖cartesianGradeCoordinates phase grade (sliceProjection phase parameterN insideN
          (seedInverseCore phase parameterM insideM field))‖ := by
    rw [seedMatrixCore_eq_full phase parameterN insideN]
    exact smoothMultiplier_coordinates_bound (grade := grade) phase _ _ _
  have multiplierNonneg := multiplierConstant_nonnegative grade phase.gamma phase.gamma_pos.le
  have matrixEnvNonneg := envelope_nonneg' phase grade (seedMatrixCells parameterN)
  have sliceNonneg : (0 : ℝ) ≤ 1 + gaugeCompositeGradeConstant phase parameterN grade :=
    add_nonneg zero_le_one (gaugeCompositeGradeConstant_nonneg phase parameterN grade)
  calc ‖cartesianGradeCoordinates phase grade
        (seedMatrixCore phase parameterN insideN (sliceProjection phase parameterN insideN
          (seedInverseCore phase parameterM insideM field)))‖
      ≤ multiplierConstant grade phase.gamma * envelope phase grade (seedMatrixCells parameterN) *
          ‖cartesianGradeCoordinates phase grade (sliceProjection phase parameterN insideN
            (seedInverseCore phase parameterM insideM field))‖ := matrixBound
    _ ≤ multiplierConstant grade phase.gamma * envelope phase grade (seedMatrixCells parameterN) *
          ((1 + gaugeCompositeGradeConstant phase parameterN grade) *
            (multiplierConstant grade phase.gamma *
              envelope phase grade (seedInverseCells parameterM) *
                ‖cartesianGradeCoordinates phase grade field‖)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg multiplierNonneg matrixEnvNonneg)
        exact sliceBound.trans (mul_le_mul_of_nonneg_left inverseBound sliceNonneg)
    _ = planarTransferGradeConstant phase parameterM parameterN grade *
          ‖cartesianGradeCoordinates phase grade field‖ := by
        unfold planarTransferGradeConstant
        ring

/-- Grade constant of the complete transfer. -/
def seedTransferGradeConstant (grade : ℕ) : ℝ :=
  planarTransferGradeConstant phase parameterM parameterN grade +
    ((1 + orthogonalGradeConstant grade) + ‖(phase.length⁻¹ : ℂ)‖ *
      (orthogonalGradeConstant grade *
        ((coordinateRowConstant grade * (multiplierConstant grade phase.gamma *
            envelope phase grade (derivativeRowCoefficients parameterN 0)) +
          coordinateRowConstant grade * (multiplierConstant grade phase.gamma *
            envelope phase grade (derivativeRowCoefficients parameterN 1))) *
          planarTransferGradeConstant phase parameterM parameterN grade)))

theorem seedTransfer_coordinates_bound {grade : ℕ} (field : ACore phase 3) :
    ‖cartesianGradeCoordinates phase grade
        (seedTransfer phase parameterM insideM parameterN insideN field)‖ ≤
      seedTransferGradeConstant phase parameterM parameterN grade *
        ‖cartesianGradeCoordinates phase grade field‖ := by
  have planarPartBound : ‖cartesianGradeCoordinates phase grade
      (planarPartCore phase field)‖ ≤ ‖cartesianGradeCoordinates phase grade field‖ :=
    valueMapCore_coordinates_le_one phase planarPartMap planarPartMap_norm_le field
  have toroidalPartBound : ‖cartesianGradeCoordinates phase grade
      (toroidalPartCore phase field)‖ ≤ ‖cartesianGradeCoordinates phase grade field‖ :=
    valueMapCore_coordinates_le_one phase toroidalPartMap toroidalPartMap_norm_le field
  have planarBound : ‖cartesianGradeCoordinates phase grade
      (planarTransfer phase parameterM insideM parameterN insideN
        (planarPartCore phase field))‖ ≤
      planarTransferGradeConstant phase parameterM parameterN grade *
        ‖cartesianGradeCoordinates phase grade field‖ :=
    (planarTransfer_coordinates_bound phase parameterM insideM parameterN insideN _).trans
      (mul_le_mul_of_nonneg_left planarPartBound
        (planarTransferGradeConstant_nonneg phase parameterM parameterN grade))
  have dotBound : ‖cartesianGradeCoordinates phase grade
      (derivativeDotCore phase parameterN insideN
        (planarTransfer phase parameterM insideM parameterN insideN
          (planarPartCore phase field)))‖ ≤
      (coordinateRowConstant grade * (multiplierConstant grade phase.gamma *
          envelope phase grade (derivativeRowCoefficients parameterN 0)) +
        coordinateRowConstant grade * (multiplierConstant grade phase.gamma *
          envelope phase grade (derivativeRowCoefficients parameterN 1))) *
        (planarTransferGradeConstant phase parameterM parameterN grade *
          ‖cartesianGradeCoordinates phase grade field‖) := by
    have rowsNonneg : (0 : ℝ) ≤ coordinateRowConstant grade *
        (multiplierConstant grade phase.gamma *
          envelope phase grade (derivativeRowCoefficients parameterN 0)) +
        coordinateRowConstant grade * (multiplierConstant grade phase.gamma *
          envelope phase grade (derivativeRowCoefficients parameterN 1)) := by
      have first := coordinateRowConstant_nonneg grade
      have second := multiplierConstant_nonnegative grade phase.gamma phase.gamma_pos.le
      have third := envelope_nonneg phase grade (derivativeRowCoefficients parameterN 0)
      have fourth := envelope_nonneg phase grade (derivativeRowCoefficients parameterN 1)
      positivity
    have splitApply : derivativeDotCore phase parameterN insideN
        (planarTransfer phase parameterM insideM parameterN insideN
          (planarPartCore phase field)) =
        coordinateCore phase 0 (smoothMultiplier phase (derivativeRowCoefficients parameterN 0)
          (derivativeRowCoefficients_envelope_summable phase parameterN insideN 0)
          (planarTransfer phase parameterM insideM parameterN insideN
            (planarPartCore phase field))) +
        coordinateCore phase 1 (smoothMultiplier phase (derivativeRowCoefficients parameterN 1)
          (derivativeRowCoefficients_envelope_summable phase parameterN insideN 1)
          (planarTransfer phase parameterM insideM parameterN insideN
            (planarPartCore phase field))) := rfl
    rw [splitApply, map_add]
    have termBound (coordinate : Fin 2) : ‖cartesianGradeCoordinates phase grade
        (coordinateCore phase coordinate (smoothMultiplier phase
          (derivativeRowCoefficients parameterN coordinate)
          (derivativeRowCoefficients_envelope_summable phase parameterN insideN coordinate)
          (planarTransfer phase parameterM insideM parameterN insideN
            (planarPartCore phase field))))‖ ≤
        coordinateRowConstant grade * (multiplierConstant grade phase.gamma *
          envelope phase grade (derivativeRowCoefficients parameterN coordinate)) *
          (planarTransferGradeConstant phase parameterM parameterN grade *
            ‖cartesianGradeCoordinates phase grade field‖) := by
      have rowNonneg := mul_nonneg
        (multiplierConstant_nonnegative grade phase.gamma phase.gamma_pos.le)
        (envelope_nonneg phase grade (derivativeRowCoefficients parameterN coordinate))
      calc ‖cartesianGradeCoordinates phase grade (coordinateCore phase coordinate
            (smoothMultiplier phase (derivativeRowCoefficients parameterN coordinate)
              (derivativeRowCoefficients_envelope_summable phase parameterN insideN coordinate)
              (planarTransfer phase parameterM insideM parameterN insideN
                (planarPartCore phase field))))‖
          ≤ coordinateRowConstant grade * ‖cartesianGradeCoordinates phase grade
              (smoothMultiplier phase (derivativeRowCoefficients parameterN coordinate)
                (derivativeRowCoefficients_envelope_summable phase parameterN insideN
                  coordinate)
                (planarTransfer phase parameterM insideM parameterN insideN
                  (planarPartCore phase field)))‖ :=
            coordinateCore_coordinates_bound phase coordinate _ grade
        _ ≤ coordinateRowConstant grade * (multiplierConstant grade phase.gamma *
              envelope phase grade (derivativeRowCoefficients parameterN coordinate) *
                ‖cartesianGradeCoordinates phase grade
                  (planarTransfer phase parameterM insideM parameterN insideN
                    (planarPartCore phase field))‖) :=
            mul_le_mul_of_nonneg_left
              (smoothMultiplier_coordinates_bound (grade := grade) phase _ _ _)
              (coordinateRowConstant_nonneg grade)
        _ ≤ coordinateRowConstant grade * (multiplierConstant grade phase.gamma *
              envelope phase grade (derivativeRowCoefficients parameterN coordinate) *
                (planarTransferGradeConstant phase parameterM parameterN grade *
                  ‖cartesianGradeCoordinates phase grade field‖)) := by
            apply mul_le_mul_of_nonneg_left _ (coordinateRowConstant_nonneg grade)
            exact mul_le_mul_of_nonneg_left planarBound rowNonneg
        _ = _ := by ring
    calc ‖cartesianGradeCoordinates phase grade (coordinateCore phase 0 (smoothMultiplier phase
            (derivativeRowCoefficients parameterN 0)
            (derivativeRowCoefficients_envelope_summable phase parameterN insideN 0)
            (planarTransfer phase parameterM insideM parameterN insideN
              (planarPartCore phase field)))) +
          cartesianGradeCoordinates phase grade (coordinateCore phase 1 (smoothMultiplier phase
            (derivativeRowCoefficients parameterN 1)
            (derivativeRowCoefficients_envelope_summable phase parameterN insideN 1)
            (planarTransfer phase parameterM insideM parameterN insideN
              (planarPartCore phase field))))‖
        ≤ ‖cartesianGradeCoordinates phase grade (coordinateCore phase 0 (smoothMultiplier phase
              (derivativeRowCoefficients parameterN 0)
              (derivativeRowCoefficients_envelope_summable phase parameterN insideN 0)
              (planarTransfer phase parameterM insideM parameterN insideN
                (planarPartCore phase field))))‖ +
            ‖cartesianGradeCoordinates phase grade (coordinateCore phase 1 (smoothMultiplier
              phase (derivativeRowCoefficients parameterN 1)
              (derivativeRowCoefficients_envelope_summable phase parameterN insideN 1)
              (planarTransfer phase parameterM insideM parameterN insideN
                (planarPartCore phase field))))‖ := norm_add_le _ _
      _ ≤ _ := by
          rw [add_mul]
          exact add_le_add (termBound 0) (termBound 1)
  have componentBound : ‖cartesianGradeCoordinates phase grade
      (transferToroidalComponent phase parameterM insideM parameterN insideN field)‖ ≤
      ((1 + orthogonalGradeConstant grade) + ‖(phase.length⁻¹ : ℂ)‖ *
        (orthogonalGradeConstant grade *
          ((coordinateRowConstant grade * (multiplierConstant grade phase.gamma *
              envelope phase grade (derivativeRowCoefficients parameterN 0)) +
            coordinateRowConstant grade * (multiplierConstant grade phase.gamma *
              envelope phase grade (derivativeRowCoefficients parameterN 1))) *
            planarTransferGradeConstant phase parameterM parameterN grade))) *
        ‖cartesianGradeCoordinates phase grade field‖ := by
    have componentExpand : transferToroidalComponent phase parameterM insideM parameterN
        insideN field =
        (toroidalPartCore phase field - angularCore phase 0 (toroidalPartCore phase field)) -
          (phase.length⁻¹ : ℂ) • angularCore phase 0 (derivativeDotCore phase parameterN
            insideN (planarTransfer phase parameterM insideM parameterN insideN
              (planarPartCore phase field))) := rfl
    rw [componentExpand, map_sub, map_sub, map_smul]
    have angularToroidal := (angularCore_coordinates_bound phase 0
      (toroidalPartCore phase field) grade).trans
      (mul_le_mul_of_nonneg_left toroidalPartBound (orthogonalGradeConstant_nonnegative grade))
    have angularDot := (angularCore_coordinates_bound phase 0 (derivativeDotCore phase
      parameterN insideN (planarTransfer phase parameterM insideM parameterN insideN
        (planarPartCore phase field))) grade).trans
      (mul_le_mul_of_nonneg_left dotBound (orthogonalGradeConstant_nonnegative grade))
    calc ‖(cartesianGradeCoordinates phase grade (toroidalPartCore phase field) -
            cartesianGradeCoordinates phase grade (angularCore phase 0
              (toroidalPartCore phase field))) -
          (phase.length⁻¹ : ℂ) • cartesianGradeCoordinates phase grade (angularCore phase 0
            (derivativeDotCore phase parameterN insideN
              (planarTransfer phase parameterM insideM parameterN insideN
                (planarPartCore phase field))))‖
        ≤ ‖cartesianGradeCoordinates phase grade (toroidalPartCore phase field)‖ +
            ‖cartesianGradeCoordinates phase grade (angularCore phase 0
              (toroidalPartCore phase field))‖ +
            ‖(phase.length⁻¹ : ℂ)‖ * ‖cartesianGradeCoordinates phase grade
              (angularCore phase 0 (derivativeDotCore phase parameterN insideN
                (planarTransfer phase parameterM insideM parameterN insideN
                  (planarPartCore phase field))))‖ := by
          calc ‖_ - _‖ ≤ ‖cartesianGradeCoordinates phase grade
                  (toroidalPartCore phase field) -
                cartesianGradeCoordinates phase grade (angularCore phase 0
                  (toroidalPartCore phase field))‖ +
                ‖(phase.length⁻¹ : ℂ) • cartesianGradeCoordinates phase grade
                  (angularCore phase 0 (derivativeDotCore phase parameterN insideN
                    (planarTransfer phase parameterM insideM parameterN insideN
                      (planarPartCore phase field))))‖ := norm_sub_le _ _
            _ ≤ _ := by
                rw [norm_smul]
                exact add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ _ := by
          have expandGoal : ((1 + orthogonalGradeConstant grade) + ‖(phase.length⁻¹ : ℂ)‖ *
              (orthogonalGradeConstant grade *
                ((coordinateRowConstant grade * (multiplierConstant grade phase.gamma *
                    envelope phase grade (derivativeRowCoefficients parameterN 0)) +
                  coordinateRowConstant grade * (multiplierConstant grade phase.gamma *
                    envelope phase grade (derivativeRowCoefficients parameterN 1))) *
                  planarTransferGradeConstant phase parameterM parameterN grade))) *
              ‖cartesianGradeCoordinates phase grade field‖ =
              ‖cartesianGradeCoordinates phase grade field‖ +
              orthogonalGradeConstant grade * ‖cartesianGradeCoordinates phase grade field‖ +
              ‖(phase.length⁻¹ : ℂ)‖ * (orthogonalGradeConstant grade *
                ((coordinateRowConstant grade * (multiplierConstant grade phase.gamma *
                    envelope phase grade (derivativeRowCoefficients parameterN 0)) +
                  coordinateRowConstant grade * (multiplierConstant grade phase.gamma *
                    envelope phase grade (derivativeRowCoefficients parameterN 1))) *
                  (planarTransferGradeConstant phase parameterM parameterN grade *
                    ‖cartesianGradeCoordinates phase grade field‖))) := by ring
          rw [expandGoal]
          exact add_le_add (add_le_add toroidalPartBound angularToroidal)
            (mul_le_mul_of_nonneg_left (by
              apply angularDot.trans
              apply mul_le_mul_of_nonneg_left _ (orthogonalGradeConstant_nonnegative grade)
              exact le_of_eq (by ring)) (norm_nonneg _))
  have inclusionPlanar := valueMapCore_coordinates_le_one (grade := grade) phase
    planarInclusionMap planarInclusionMap_norm_le
    (planarTransfer phase parameterM insideM parameterN insideN (planarPartCore phase field))
  have inclusionToroidal := valueMapCore_coordinates_le_one (grade := grade) phase
    toroidalInclusionMap toroidalInclusionMap_norm_le
    (transferToroidalComponent phase parameterM insideM parameterN insideN field)
  calc ‖cartesianGradeCoordinates phase grade
        (seedTransfer phase parameterM insideM parameterN insideN field)‖
      = ‖cartesianGradeCoordinates phase grade
          (planarInclusionCore phase (planarTransfer phase parameterM insideM parameterN
            insideN (planarPartCore phase field)) +
          toroidalInclusionCore phase (transferToroidalComponent phase parameterM insideM
            parameterN insideN field))‖ := rfl
    _ = ‖cartesianGradeCoordinates phase grade
          (planarInclusionCore phase (planarTransfer phase parameterM insideM parameterN
            insideN (planarPartCore phase field))) +
          cartesianGradeCoordinates phase grade (toroidalInclusionCore phase
            (transferToroidalComponent phase parameterM insideM parameterN insideN field))‖ :=
        by rw [map_add]
    _ ≤ ‖cartesianGradeCoordinates phase grade
          (planarInclusionCore phase (planarTransfer phase parameterM insideM parameterN
            insideN (planarPartCore phase field)))‖ +
          ‖cartesianGradeCoordinates phase grade (toroidalInclusionCore phase
            (transferToroidalComponent phase parameterM insideM parameterN insideN field))‖ :=
        norm_add_le _ _
    _ ≤ seedTransferGradeConstant phase parameterM parameterN grade *
          ‖cartesianGradeCoordinates phase grade field‖ := by
        unfold seedTransferGradeConstant
        rw [add_mul]
        exact add_le_add (inclusionPlanar.trans planarBound)
          (inclusionToroidal.trans componentBound)

/-- The transfer preserves zero first Cartesian jets. -/
theorem seedTransfer_zero_first_jets (field : ACore phase 3)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.1 cell)) :
    ∀ cell, ZeroCartesianFirstJets
      ((seedTransfer phase parameterM insideM parameterN insideN field).1 cell) := by
  have planarJets : ∀ cell, ZeroCartesianFirstJets
      ((planarTransfer phase parameterM insideM parameterN insideN
        (planarPartCore phase field)).1 cell) := by
    have inverseJets : ∀ cell, ZeroCartesianFirstJets
        ((seedInverseCore phase parameterM insideM (planarPartCore phase field)).1 cell) := by
      intro cell
      rw [seedInverseCore_eq_full phase parameterM insideM]
      exact smoothMultiplier_preserves_zero_first_jets phase _
        (seedInverseCells_envelope_summable phase parameterM insideM) _
        (valueMapCore_zero_first_jets phase planarPartMap field zeroJets) cell
    have sliceJets : ∀ cell, ZeroCartesianFirstJets
        ((sliceProjection phase parameterN insideN
          (seedInverseCore phase parameterM insideM (planarPartCore phase field))).1 cell) := by
      intro cell
      rw [sliceProjection_apply]
      change ZeroCartesianFirstJets
        ((seedInverseCore phase parameterM insideM (planarPartCore phase field)).1 cell -
          (gaugeComposite phase parameterN insideN (seedInverseCore phase parameterM insideM
            (planarPartCore phase field))).1 cell)
      apply zeroJets_sub (inverseJets cell)
      rw [gaugeComposite_apply]
      exact tangentialCore_zero_first_jets phase _
        (seedTransposeCore_zero_first_jets phase parameterN insideN _
          (seedMatrixCore_zero_first_jets phase parameterN insideN _ inverseJets)) cell
    intro cell
    rw [planarTransfer_apply]
    exact seedMatrixCore_zero_first_jets phase parameterN insideN _ sliceJets cell
  intro cell
  change ZeroCartesianFirstJets
    ((planarInclusionCore phase (planarTransfer phase parameterM insideM parameterN insideN
        (planarPartCore phase field))).1 cell +
      (toroidalInclusionCore phase (transferToroidalComponent phase parameterM insideM
        parameterN insideN field)).1 cell)
  apply zeroJets_add
  · exact valueMapCore_zero_first_jets phase planarInclusionMap _ planarJets cell
  · apply valueMapCore_zero_first_jets phase toroidalInclusionMap _ ?_ cell
    intro innerCell
    change ZeroCartesianFirstJets
      (((toroidalPartCore phase field - angularCore phase 0 (toroidalPartCore phase field)) -
        (phase.length⁻¹ : ℂ) • angularCore phase 0 (derivativeDotCore phase parameterN insideN
          (planarTransfer phase parameterM insideM parameterN insideN
            (planarPartCore phase field)))).1 innerCell)
    have toroidalJets := valueMapCore_zero_first_jets phase toroidalPartMap field zeroJets
    have angularToroidalJets := angularCore_zero_first_jets phase 0 _ toroidalJets
    have dotJets := derivativeDotCore_zero_first_jets phase parameterN insideN _
      planarJets
    have angularDotJets := angularCore_zero_first_jets phase 0 _ dotJets
    change ZeroCartesianFirstJets
      (((toroidalPartCore phase field - angularCore phase 0 (toroidalPartCore phase field)).1
          innerCell) -
        (((phase.length⁻¹ : ℂ) • angularCore phase 0 (derivativeDotCore phase parameterN
          insideN (planarTransfer phase parameterM insideM parameterN insideN
            (planarPartCore phase field)))).1 innerCell))
    apply zeroJets_sub
    · change ZeroCartesianFirstJets ((toroidalPartCore phase field).1 innerCell -
        (angularCore phase 0 (toroidalPartCore phase field)).1 innerCell)
      exact zeroJets_sub (toroidalJets innerCell) (angularToroidalJets innerCell)
    · change ZeroCartesianFirstJets ((phase.length⁻¹ : ℂ) •
        (angularCore phase 0 (derivativeDotCore phase parameterN insideN
          (planarTransfer phase parameterM insideM parameterN insideN
            (planarPartCore phase field)))).1 innerCell)
      exact zeroJets_smul _ (angularDotJets innerCell)

end Grad.Constraints.Gauges
