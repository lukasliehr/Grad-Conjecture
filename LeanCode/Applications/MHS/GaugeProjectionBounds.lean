import GaugeProjectionMaps

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers

variable (phase : PhaseParameters) (parameter : Seed.Parameters)

theorem ofCoreLinear_norm_coordinates {dimension grade : ℕ} (field : ACore phase dimension) :
    ‖GradeCore.ofCoreLinear (grade := grade) field‖ =
      ‖cartesianGradeCoordinates phase grade field‖ := by
  rw [gradeCore_norm_eq_cartesianGradeSeminorm, cartesianGradeSeminorm_apply,
    gradeCoreCoordinates_apply]
  rfl

theorem envelope_nonneg (grade : ℕ)
    (coefficients : ℤ → ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 1) :
    0 ≤ envelope phase grade coefficients :=
  tsum_nonneg (fun cell => envelopeTerm_nonnegative phase grade coefficients cell)

theorem envelope_nonneg' (grade : ℕ)
    (coefficients : ℤ → ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) :
    0 ≤ envelope phase grade coefficients :=
  tsum_nonneg (fun cell => envelopeTerm_nonnegative phase grade coefficients cell)

theorem planarPartMap_norm_le : ‖planarPartMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro value
  rw [one_mul, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  rw [Fin.sum_univ_two, Fin.sum_univ_three]
  change ‖value 0‖ ^ 2 + ‖value 1‖ ^ 2 ≤ ‖value 0‖ ^ 2 + ‖value 1‖ ^ 2 + ‖value 2‖ ^ 2
  have := sq_nonneg ‖value 2‖
  linarith

theorem planarInclusionMap_norm_le : ‖planarInclusionMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro value
  rw [one_mul, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  rw [Fin.sum_univ_two, Fin.sum_univ_three]
  change ‖value 0‖ ^ 2 + ‖value 1‖ ^ 2 + ‖(0 : ℂ)‖ ^ 2 ≤ ‖value 0‖ ^ 2 + ‖value 1‖ ^ 2
  simp

theorem toroidalPartMap_norm_le : ‖toroidalPartMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro value
  rw [one_mul, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  rw [Fin.sum_univ_one, Fin.sum_univ_three]
  change ‖value 2‖ ^ 2 ≤ ‖value 0‖ ^ 2 + ‖value 1‖ ^ 2 + ‖value 2‖ ^ 2
  have first := sq_nonneg ‖value 0‖
  have second := sq_nonneg ‖value 1‖
  linarith

theorem toroidalInclusionMap_norm_le : ‖toroidalInclusionMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro value
  rw [one_mul, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  rw [Fin.sum_univ_one, Fin.sum_univ_three]
  change ‖(0 : ℂ)‖ ^ 2 + ‖(0 : ℂ)‖ ^ 2 + ‖value 0‖ ^ 2 ≤ ‖value 0‖ ^ 2
  simp

theorem tangentialCore_coordinates_bound {grade : ℕ} (field : ACore phase 2) :
    ‖cartesianGradeCoordinates phase grade (tangentialCore phase field)‖ ≤
      tangentialGradeConstant grade * ‖cartesianGradeCoordinates phase grade field‖ := by
  rw [← ofCoreLinear_norm_coordinates, ← ofCoreLinear_norm_coordinates]
  have identify : GradeCore.ofCoreLinear (grade := grade) (tangentialCore phase field) =
      tangentialGradeCore phase (GradeCore.ofCoreLinear field) :=
    GradeCore.toCore_injective rfl
  rw [identify]
  exact tangentialGradeCore_norm_le phase _

theorem smoothMultiplier_coordinates_bound {sourceDimension targetDimension grade : ℕ}
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (summable : ∀ grade, Summable (envelopeTerm phase grade coefficients))
    (field : ACore phase sourceDimension) :
    ‖cartesianGradeCoordinates phase grade (smoothMultiplier phase coefficients summable field)‖ ≤
      multiplierConstant grade phase.gamma * envelope phase grade coefficients *
        ‖cartesianGradeCoordinates phase grade field‖ := by
  rw [← ofCoreLinear_norm_coordinates, ← ofCoreLinear_norm_coordinates]
  exact smoothMultiplier_bound phase coefficients summable field grade

/-- The explicit poloidal same-grade constant. -/
def poloidalGradeConstant (grade : ℕ) : ℝ :=
  multiplierConstant grade phase.gamma * envelope phase grade (seedMatrixCells parameter) *
    (tangentialGradeConstant grade *
      (multiplierConstant grade phase.gamma * envelope phase grade (seedTransposeCells parameter)))

/-- The explicit toroidal same-grade constant. -/
def toroidalGradeConstant (grade : ℕ) : ℝ :=
  orthogonalGradeConstant grade *
    (1 + ‖(phase.length⁻¹ : ℂ)‖ *
      (coordinateRowConstant grade * (multiplierConstant grade phase.gamma *
          envelope phase grade (derivativeRowCoefficients parameter 0)) +
        coordinateRowConstant grade * (multiplierConstant grade phase.gamma *
          envelope phase grade (derivativeRowCoefficients parameter 1))))

theorem poloidalGradeConstant_nonneg (grade : ℕ) :
    0 ≤ poloidalGradeConstant phase parameter grade := by
  unfold poloidalGradeConstant
  have first := multiplierConstant_nonnegative grade phase.gamma phase.gamma_pos.le
  have second := envelope_nonneg' phase grade (seedMatrixCells parameter)
  have third := tangentialGradeConstant_nonnegative grade
  have fourth := envelope_nonneg' phase grade (seedTransposeCells parameter)
  positivity

theorem toroidalGradeConstant_nonneg (grade : ℕ) :
    0 ≤ toroidalGradeConstant phase parameter grade := by
  unfold toroidalGradeConstant
  have first := orthogonalGradeConstant_nonnegative grade
  have second := multiplierConstant_nonnegative grade phase.gamma phase.gamma_pos.le
  have third := envelope_nonneg phase grade (derivativeRowCoefficients parameter 0)
  have fourth := envelope_nonneg phase grade (derivativeRowCoefficients parameter 1)
  have fifth := coordinateRowConstant_nonneg grade
  have sixth := norm_nonneg (phase.length⁻¹ : ℂ)
  positivity

theorem valueMapCore_coordinates_le_one {sourceDimension targetDimension grade : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (mappingBound : ‖mapping‖ ≤ 1) (field : ACore phase sourceDimension) :
    ‖cartesianGradeCoordinates phase grade (valueMapCore mapping phase field)‖ ≤
      ‖cartesianGradeCoordinates phase grade field‖ :=
  (valueMapCore_coordinates_bound mapping phase field grade).trans
    (by
      have := norm_nonneg (cartesianGradeCoordinates phase grade field)
      nlinarith)

/-- The exact same-grade bound of the poloidal correction. -/
theorem poloidalCorrection_coordinates_bound
    (inside : parameter ∈ Seed.parameterDomain) {grade : ℕ} (field : ACore phase 3) :
    ‖cartesianGradeCoordinates phase grade
        (poloidalCorrection phase parameter inside field)‖ ≤
      poloidalGradeConstant phase parameter grade *
        ‖cartesianGradeCoordinates phase grade field‖ := by
  rw [poloidalCorrection_apply]
  have planarBound : ‖cartesianGradeCoordinates phase grade (planarPartCore phase field)‖ ≤
      ‖cartesianGradeCoordinates phase grade field‖ :=
    valueMapCore_coordinates_le_one phase planarPartMap planarPartMap_norm_le field
  have transposeBound := smoothMultiplier_coordinates_bound (grade := grade) phase
    (seedTransposeCells parameter) (seedTransposeCells_envelope_summable phase parameter inside)
    (planarPartCore phase field)
  have tangentialBound := tangentialCore_coordinates_bound (grade := grade) phase
    (seedTransposeCore phase parameter inside (planarPartCore phase field))
  have matrixIdentify : seedMatrixCore phase parameter inside (tangentialCore phase
      (seedTransposeCore phase parameter inside (planarPartCore phase field))) =
      smoothMultiplier phase (seedMatrixCells parameter)
        (seedMatrixCells_envelope_summable phase parameter inside)
        (tangentialCore phase (seedTransposeCore phase parameter inside
          (planarPartCore phase field))) :=
    seedMatrixCore_eq_full phase parameter inside _
  have matrixBound := smoothMultiplier_coordinates_bound (grade := grade) phase
    (seedMatrixCells parameter) (seedMatrixCells_envelope_summable phase parameter inside)
    (tangentialCore phase (seedTransposeCore phase parameter inside
      (planarPartCore phase field)))
  have inclusionBound : ‖cartesianGradeCoordinates phase grade
      (planarInclusionCore phase (seedMatrixCore phase parameter inside (tangentialCore phase
        (seedTransposeCore phase parameter inside (planarPartCore phase field)))))‖ ≤
      ‖cartesianGradeCoordinates phase grade
        (seedMatrixCore phase parameter inside (tangentialCore phase
          (seedTransposeCore phase parameter inside (planarPartCore phase field))))‖ :=
    valueMapCore_coordinates_le_one phase planarInclusionMap planarInclusionMap_norm_le _
  have tangentialNonneg := tangentialGradeConstant_nonnegative grade
  have multiplierNonneg := multiplierConstant_nonnegative grade phase.gamma phase.gamma_pos.le
  have matrixEnvNonneg := envelope_nonneg' phase grade (seedMatrixCells parameter)
  have transposeEnvNonneg := envelope_nonneg' phase grade (seedTransposeCells parameter)
  calc ‖cartesianGradeCoordinates phase grade
        (planarInclusionCore phase (seedMatrixCore phase parameter inside (tangentialCore phase
          (seedTransposeCore phase parameter inside (planarPartCore phase field)))))‖
      ≤ ‖cartesianGradeCoordinates phase grade
          (seedMatrixCore phase parameter inside (tangentialCore phase
            (seedTransposeCore phase parameter inside (planarPartCore phase field))))‖ :=
        inclusionBound
    _ ≤ multiplierConstant grade phase.gamma * envelope phase grade (seedMatrixCells parameter) *
          ‖cartesianGradeCoordinates phase grade (tangentialCore phase
            (seedTransposeCore phase parameter inside (planarPartCore phase field)))‖ := by
        rw [matrixIdentify]
        exact matrixBound
    _ ≤ poloidalGradeConstant phase parameter grade *
          ‖cartesianGradeCoordinates phase grade field‖ := by
        unfold poloidalGradeConstant
        have chain : ‖cartesianGradeCoordinates phase grade (tangentialCore phase
            (seedTransposeCore phase parameter inside (planarPartCore phase field)))‖ ≤
            tangentialGradeConstant grade * (multiplierConstant grade phase.gamma *
              envelope phase grade (seedTransposeCells parameter) *
                ‖cartesianGradeCoordinates phase grade field‖) :=
          tangentialBound.trans (mul_le_mul_of_nonneg_left
            (transposeBound.trans (mul_le_mul_of_nonneg_left planarBound
              (mul_nonneg multiplierNonneg transposeEnvNonneg))) tangentialNonneg)
        nlinarith [norm_nonneg (cartesianGradeCoordinates phase grade (tangentialCore phase
          (seedTransposeCore phase parameter inside (planarPartCore phase field)))),
          mul_nonneg multiplierNonneg matrixEnvNonneg]

/-- The exact same-grade bound of the toroidal correction. -/
theorem toroidalCorrection_coordinates_bound
    (inside : parameter ∈ Seed.parameterDomain) {grade : ℕ} (field : ACore phase 3) :
    ‖cartesianGradeCoordinates phase grade
        (toroidalCorrection phase parameter inside field)‖ ≤
      toroidalGradeConstant phase parameter grade *
        ‖cartesianGradeCoordinates phase grade field‖ := by
  rw [toroidalCorrection_apply]
  have inclusionBound := valueMapCore_coordinates_le_one (grade := grade) phase
    toroidalInclusionMap toroidalInclusionMap_norm_le
    (angularCore phase 0 (toroidalPartCore phase field +
      (phase.length⁻¹ : ℂ) • derivativeDotCore phase parameter inside
        (planarPartCore phase field)))
  have angularBound := angularCore_coordinates_bound phase 0
    (toroidalPartCore phase field +
      (phase.length⁻¹ : ℂ) • derivativeDotCore phase parameter inside
        (planarPartCore phase field)) grade
  have toroidalBound : ‖cartesianGradeCoordinates phase grade (toroidalPartCore phase field)‖ ≤
      ‖cartesianGradeCoordinates phase grade field‖ :=
    valueMapCore_coordinates_le_one phase toroidalPartMap toroidalPartMap_norm_le field
  have planarBound : ‖cartesianGradeCoordinates phase grade (planarPartCore phase field)‖ ≤
      ‖cartesianGradeCoordinates phase grade field‖ :=
    valueMapCore_coordinates_le_one phase planarPartMap planarPartMap_norm_le field
  have dotBound : ‖cartesianGradeCoordinates phase grade
      (derivativeDotCore phase parameter inside (planarPartCore phase field))‖ ≤
      (coordinateRowConstant grade * (multiplierConstant grade phase.gamma *
          envelope phase grade (derivativeRowCoefficients parameter 0)) +
        coordinateRowConstant grade * (multiplierConstant grade phase.gamma *
          envelope phase grade (derivativeRowCoefficients parameter 1))) *
        ‖cartesianGradeCoordinates phase grade field‖ := by
    have splitApply : derivativeDotCore phase parameter inside (planarPartCore phase field) =
        coordinateCore phase 0 (smoothMultiplier phase (derivativeRowCoefficients parameter 0)
          (derivativeRowCoefficients_envelope_summable phase parameter inside 0)
          (planarPartCore phase field)) +
        coordinateCore phase 1 (smoothMultiplier phase (derivativeRowCoefficients parameter 1)
          (derivativeRowCoefficients_envelope_summable phase parameter inside 1)
          (planarPartCore phase field)) := rfl
    rw [splitApply, map_add]
    have firstTerm := (coordinateCore_coordinates_bound phase 0 (smoothMultiplier phase
        (derivativeRowCoefficients parameter 0)
        (derivativeRowCoefficients_envelope_summable phase parameter inside 0)
        (planarPartCore phase field)) grade).trans
      (mul_le_mul_of_nonneg_left ((smoothMultiplier_coordinates_bound (grade := grade) phase
        (derivativeRowCoefficients parameter 0)
        (derivativeRowCoefficients_envelope_summable phase parameter inside 0)
        (planarPartCore phase field)).trans (mul_le_mul_of_nonneg_left planarBound
          (mul_nonneg (multiplierConstant_nonnegative grade phase.gamma phase.gamma_pos.le)
            (envelope_nonneg phase grade (derivativeRowCoefficients parameter 0)))))
        (coordinateRowConstant_nonneg grade))
    have secondTerm := (coordinateCore_coordinates_bound phase 1 (smoothMultiplier phase
        (derivativeRowCoefficients parameter 1)
        (derivativeRowCoefficients_envelope_summable phase parameter inside 1)
        (planarPartCore phase field)) grade).trans
      (mul_le_mul_of_nonneg_left ((smoothMultiplier_coordinates_bound (grade := grade) phase
        (derivativeRowCoefficients parameter 1)
        (derivativeRowCoefficients_envelope_summable phase parameter inside 1)
        (planarPartCore phase field)).trans (mul_le_mul_of_nonneg_left planarBound
          (mul_nonneg (multiplierConstant_nonnegative grade phase.gamma phase.gamma_pos.le)
            (envelope_nonneg phase grade (derivativeRowCoefficients parameter 1)))))
        (coordinateRowConstant_nonneg grade))
    calc ‖cartesianGradeCoordinates phase grade (coordinateCore phase 0 (smoothMultiplier phase
            (derivativeRowCoefficients parameter 0)
            (derivativeRowCoefficients_envelope_summable phase parameter inside 0)
            (planarPartCore phase field))) +
          cartesianGradeCoordinates phase grade (coordinateCore phase 1 (smoothMultiplier phase
            (derivativeRowCoefficients parameter 1)
            (derivativeRowCoefficients_envelope_summable phase parameter inside 1)
            (planarPartCore phase field)))‖
        ≤ ‖cartesianGradeCoordinates phase grade (coordinateCore phase 0 (smoothMultiplier phase
              (derivativeRowCoefficients parameter 0)
              (derivativeRowCoefficients_envelope_summable phase parameter inside 0)
              (planarPartCore phase field)))‖ +
            ‖cartesianGradeCoordinates phase grade (coordinateCore phase 1 (smoothMultiplier phase
              (derivativeRowCoefficients parameter 1)
              (derivativeRowCoefficients_envelope_summable phase parameter inside 1)
              (planarPartCore phase field)))‖ := norm_add_le _ _
      _ ≤ _ := by
          rw [add_mul]
          exact add_le_add
            (firstTerm.trans_eq (by ring)) (secondTerm.trans_eq (by ring))
  calc ‖cartesianGradeCoordinates phase grade
        (toroidalInclusionCore phase (angularCore phase 0
          (toroidalPartCore phase field +
            (phase.length⁻¹ : ℂ) • derivativeDotCore phase parameter inside
              (planarPartCore phase field))))‖
      ≤ ‖cartesianGradeCoordinates phase grade (angularCore phase 0
          (toroidalPartCore phase field +
            (phase.length⁻¹ : ℂ) • derivativeDotCore phase parameter inside
              (planarPartCore phase field)))‖ := inclusionBound
    _ ≤ orthogonalGradeConstant grade * ‖cartesianGradeCoordinates phase grade
          (toroidalPartCore phase field +
            (phase.length⁻¹ : ℂ) • derivativeDotCore phase parameter inside
              (planarPartCore phase field))‖ := angularBound
    _ ≤ toroidalGradeConstant phase parameter grade *
          ‖cartesianGradeCoordinates phase grade field‖ := by
        unfold toroidalGradeConstant
        have insideBound : ‖cartesianGradeCoordinates phase grade
            (toroidalPartCore phase field +
              (phase.length⁻¹ : ℂ) • derivativeDotCore phase parameter inside
                (planarPartCore phase field))‖ ≤
            (1 + ‖(phase.length⁻¹ : ℂ)‖ *
              (coordinateRowConstant grade * (multiplierConstant grade phase.gamma *
                  envelope phase grade (derivativeRowCoefficients parameter 0)) +
                coordinateRowConstant grade * (multiplierConstant grade phase.gamma *
                  envelope phase grade (derivativeRowCoefficients parameter 1)))) *
              ‖cartesianGradeCoordinates phase grade field‖ := by
          rw [map_add, map_smul]
          calc ‖cartesianGradeCoordinates phase grade (toroidalPartCore phase field) +
                (phase.length⁻¹ : ℂ) • cartesianGradeCoordinates phase grade
                  (derivativeDotCore phase parameter inside (planarPartCore phase field))‖
              ≤ ‖cartesianGradeCoordinates phase grade (toroidalPartCore phase field)‖ +
                ‖(phase.length⁻¹ : ℂ)‖ * ‖cartesianGradeCoordinates phase grade
                  (derivativeDotCore phase parameter inside (planarPartCore phase field))‖ := by
                rw [← norm_smul (phase.length⁻¹ : ℂ)]
                exact norm_add_le _ _
            _ ≤ _ := by
                rw [add_mul, one_mul]
                exact add_le_add toroidalBound (by
                  rw [mul_assoc]
                  exact mul_le_mul_of_nonneg_left dotBound (norm_nonneg _))
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left insideBound (orthogonalGradeConstant_nonnegative grade)

end Grad.Constraints.Gauges
