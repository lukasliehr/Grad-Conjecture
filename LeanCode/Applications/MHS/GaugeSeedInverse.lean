import GaugeSeedTrace

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators Matrix

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Frame

local instance gaugeInversePeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem operator_ext_of_entries (first second : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (entries : ∀ row column, operatorEntry first row column = operatorEntry second row column) :
    first = second := by
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro coordinate
  rw [operator_apply_coordinates, operator_apply_coordinates, entries, entries]

theorem actualInverseOperator_entry (parameter : Seed.Parameters) (angle : ℝ)
    (row column : Fin 2) :
    operatorEntry (Seed.actualInverseOperator parameter angle) row column =
      (Seed.actualInverse parameter angle row column : ℂ) := by
  unfold operatorEntry Seed.actualInverseOperator
  rw [Grad.GaugeCoefficients.Physical.matrixEmbedding_apply, Fin.sum_univ_two,
    planarBasis_apply, planarBasis_apply]
  fin_cases column <;> simp

/-- The literal two-sided seed inverse law at the operator level. -/
theorem inverse_matrix_operator_id (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (angle : ℝ) :
    (Seed.actualInverseOperator parameter angle).comp
        (harmonicSeedOperator (parameter 0) (parameter 1) (parameter 2) (parameter 3) angle) =
      ContinuousLinearMap.id ℂ (ComplexEuclidean 2) := by
  have algebra := (Seed.actualSeedAlgebra parameter inside angle).2.2.2.2
  apply operator_ext_of_entries
  intro row column
  rw [operatorEntry_comp, actualInverseOperator_entry, actualInverseOperator_entry,
    harmonicSeedOperator_entry, harmonicSeedOperator_entry]
  have productEntry : (Seed.actualInverse parameter angle * Seed.actualMatrix parameter angle)
      row column = (1 : Matrix (Fin 2) (Fin 2) ℝ) row column := by
    rw [algebra]
  rw [Matrix.mul_apply, Fin.sum_univ_two] at productEntry
  have identityEntry : operatorEntry (ContinuousLinearMap.id ℂ (ComplexEuclidean 2)) row column =
      ((1 : Matrix (Fin 2) (Fin 2) ℝ) row column : ℂ) := by
    unfold operatorEntry
    rw [ContinuousLinearMap.id_apply, planarBasis_apply, Matrix.one_apply]
    by_cases equal : row = column
    · rw [if_pos equal, if_pos equal]
      norm_num
    · rw [if_neg equal, if_neg equal]
      norm_num
  rw [identityEntry, ← productEntry]
  push_cast
  ring

/-- Exact operator delta law for the convolution of the full inverse and
matrix seed families. -/
theorem seedInverseConvolution_delta (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) :
    (∀ target : ℤ, Summable (fun shift =>
      (seedInverseCells parameter shift).comp (seedMatrixCells parameter (target - shift)))) ∧
    ∀ target : ℤ, (∑' shift, (seedInverseCells parameter shift).comp
        (seedMatrixCells parameter (target - shift))) =
      if target = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0 := by
  have firstNorms := seedInverseCells_norm_summable phase parameter inside
  have secondNorms := seedMatrixCells_norm_summable phase parameter inside
  obtain ⟨rowNorms, totalNorms⟩ := convolution_norm_rows _ _ firstNorms secondNorms
  have convSummable (target : ℤ) : Summable (fun shift =>
      (seedInverseCells parameter shift).comp (seedMatrixCells parameter (target - shift))) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun shift => ContinuousLinearMap.opNorm_comp_le _ _) (rowNorms target))
  refine ⟨convSummable, ?_⟩
  set convRow : ℤ → ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2 := fun target =>
    ∑' shift, (seedInverseCells parameter shift).comp
      (seedMatrixCells parameter (target - shift)) with convRow_def
  set deltaRow : ℤ → ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2 := fun target =>
    if target = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0 with deltaRow_def
  have convRowNormBound (target : ℤ) : ‖convRow target‖ ≤
      ∑' shift, ‖seedInverseCells parameter shift‖ *
        ‖seedMatrixCells parameter (target - shift)‖ :=
    (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun shift => ContinuousLinearMap.opNorm_comp_le _ _) (rowNorms target))).trans
      ((Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun shift => ContinuousLinearMap.opNorm_comp_le _ _)
        (rowNorms target)).tsum_le_tsum
          (fun shift => ContinuousLinearMap.opNorm_comp_le _ _) (rowNorms target))
  have convRowNormSummable : Summable (fun target => ‖convRow target‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) convRowNormBound totalNorms
  have deltaRowNormSummable : Summable (fun target => ‖deltaRow target‖) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro target outside
    have nonzero : target ≠ 0 := by simpa using outside
    rw [deltaRow_def]
    simp [nonzero]
  have differenceNorms : Summable (fun target => ‖convRow target - deltaRow target‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun target => norm_sub_le _ _) (convRowNormSummable.add deltaRowNormSummable)
  have realSumIdentity (angle : ℝ) : (∑' target : ℤ,
      fourierPhase target angle • convRow target) =
      ContinuousLinearMap.id ℂ (ComplexEuclidean 2) := by
    rw [convRow_def]
    simp only
    rw [operatorComposeConvolution_fourier _ _ firstNorms secondNorms angle,
      seedInverseCells_fourier phase parameter inside angle,
      seedMatrixCells_fourier phase parameter inside angle]
    exact inverse_matrix_operator_id parameter inside angle
  have deltaSumIdentity (angle : ℝ) : (∑' target : ℤ,
      fourierPhase target angle • deltaRow target) =
      ContinuousLinearMap.id ℂ (ComplexEuclidean 2) := by
    rw [deltaRow_def]
    simp only
    exact delta_identity_fourier angle
  have circleSumZero : ∀ circle : CellCircle, (∑' target : ℤ,
      cellCharacter target circle • (convRow target - deltaRow target)) = 0 := by
    intro circle
    induction circle using QuotientAddGroup.induction_on with
    | H angle =>
      have termIdentity (target : ℤ) : cellCharacter target (angle : CellCircle) •
          (convRow target - deltaRow target) =
          fourierPhase target angle • convRow target -
            fourierPhase target angle • deltaRow target := by
        rw [cellCharacter_coe, smul_sub]
        rfl
      rw [tsum_congr termIdentity]
      have convSide : Summable (fun target => fourierPhase target angle • convRow target) := by
        apply Summable.of_norm
        simpa only [norm_smul, fourierPhase_norm, one_mul] using convRowNormSummable
      have deltaSide : Summable (fun target => fourierPhase target angle • deltaRow target) := by
        apply Summable.of_norm
        simpa only [norm_smul, fourierPhase_norm, one_mul] using deltaRowNormSummable
      rw [convSide.tsum_sub deltaSide, realSumIdentity angle, deltaSumIdentity angle, sub_self]
  intro target
  have recovered := seedCircleSeries_coefficient
    (fun index => convRow index - deltaRow index) differenceNorms target
  have zeroFunction : (fun circle : CellCircle => ∑' index : ℤ,
      cellCharacter index circle • (convRow index - deltaRow index)) =
      fun _ : CellCircle => (0 : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) :=
    funext circleSumZero
  rw [zeroFunction] at recovered
  have zeroCoefficient : fourierCoeff (T := 2 * Real.pi)
      (fun _ : CellCircle => (0 : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)) target = 0 := by
    unfold fourierCoeff
    simp
  rw [zeroCoefficient] at recovered
  have equal := sub_eq_zero.mp recovered.symm
  rw [convRow_def, deltaRow_def] at equal
  simpa using equal

/-- The full inverse multiplier is an actual left inverse of the full matrix
multiplier on the original smooth core. -/
theorem seedInverse_seedMatrix_core (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore phase 2) :
    seedInverseCore phase parameter inside (seedMatrixCore phase parameter inside field) =
      field := by
  obtain ⟨convSummable, convDelta⟩ := seedInverseConvolution_delta phase parameter inside
  rw [seedMatrixCore_eq_full phase parameter inside field,
    seedInverseCore_eq_full phase parameter inside]
  apply Subtype.ext
  funext cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have valueNorms := originalValueNorm_summable phase field point
  have valueBound (index : ℤ) : ‖(field.1 index).value point‖ ≤
      ∑' inner, ‖(field.1 inner).value point‖ :=
    valueNorms.le_tsum index (fun _ _ => norm_nonneg _)
  have valueTotalNonneg : 0 ≤ ∑' inner, ‖(field.1 inner).value point‖ :=
    tsum_nonneg (fun _ => norm_nonneg _)
  have firstNorms := seedInverseCells_norm_summable phase parameter inside
  have secondNorms := seedMatrixCells_norm_summable phase parameter inside
  have outer := smoothMultiplier_value_hasSum phase (seedInverseCells parameter)
    (seedInverseCells_envelope_summable phase parameter inside)
    (smoothMultiplier phase (seedMatrixCells parameter)
      (seedMatrixCells_envelope_summable phase parameter inside) field) cell point
  have innerValue (shift : ℤ) : ((smoothMultiplier phase (seedMatrixCells parameter)
      (seedMatrixCells_envelope_summable phase parameter inside) field).1
        (cell - shift)).value point =
      ∑' inner, seedMatrixCells parameter inner ((field.1 (cell - shift - inner)).value point) :=
    (smoothMultiplier_value_hasSum phase (seedMatrixCells parameter)
      (seedMatrixCells_envelope_summable phase parameter inside) field (cell - shift)
        point).tsum_eq.symm
  have innerSummable (shift : ℤ) : Summable (fun inner =>
      seedMatrixCells parameter inner ((field.1 (cell - shift - inner)).value point)) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun inner => ?_)
      (secondNorms.mul_right (∑' innerIndex, ‖(field.1 innerIndex).value point‖))
    exact ((seedMatrixCells parameter inner).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (valueBound _) (norm_nonneg _))
  set pairTerm : ℤ × ℤ → ComplexEuclidean 2 := fun pair =>
    seedInverseCells parameter pair.1 (seedMatrixCells parameter pair.2
      ((field.1 (cell - pair.1 - pair.2)).value point)) with pairTerm_def
  have pairBound (pair : ℤ × ℤ) : ‖pairTerm pair‖ ≤
      ‖seedInverseCells parameter pair.1‖ * (‖seedMatrixCells parameter pair.2‖ *
        ∑' innerIndex, ‖(field.1 innerIndex).value point‖) :=
    ((seedInverseCells parameter pair.1).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (((seedMatrixCells parameter pair.2).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (valueBound _) (norm_nonneg _))) (norm_nonneg _))
  have pairMajorant : Summable (fun pair : ℤ × ℤ =>
      ‖seedInverseCells parameter pair.1‖ * (‖seedMatrixCells parameter pair.2‖ *
        ∑' innerIndex, ‖(field.1 innerIndex).value point‖)) :=
    firstNorms.mul_of_nonneg (secondNorms.mul_right _) (fun _ => norm_nonneg _)
      (fun _ => mul_nonneg (norm_nonneg _) valueTotalNonneg)
  have pairNorm : Summable (fun pair : ℤ × ℤ => ‖pairTerm pair‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) pairBound pairMajorant
  have pairSummable : Summable pairTerm := pairNorm.of_norm
  have leftIterated : ((smoothMultiplier phase (seedInverseCells parameter)
      (seedInverseCells_envelope_summable phase parameter inside)
      (smoothMultiplier phase (seedMatrixCells parameter)
        (seedMatrixCells_envelope_summable phase parameter inside) field)).1 cell).value point =
      ∑' shift, ∑' inner, pairTerm (shift, inner) := by
    rw [← outer.tsum_eq]
    apply tsum_congr
    intro shift
    rw [innerValue shift, (seedInverseCells parameter shift).map_tsum (innerSummable shift)]
  have reindexedSummable : Summable (fun pair : ℤ × ℤ => pairTerm (cellConvolutionEquiv pair)) :=
    cellConvolutionEquiv.summable_iff.mpr pairSummable
  have pairIdentity : (∑' shift, ∑' inner, pairTerm (shift, inner)) =
      ∑' target, ∑' shift, pairTerm (cellConvolutionEquiv (target, shift)) := by
    rw [← pairSummable.tsum_prod, ← cellConvolutionEquiv.tsum_eq pairTerm,
      reindexedSummable.tsum_prod]
  have innerCollapse (target : ℤ) : (∑' shift, pairTerm (cellConvolutionEquiv (target, shift))) =
      (∑' shift, (seedInverseCells parameter shift).comp
        (seedMatrixCells parameter (target - shift))) ((field.1 (cell - target)).value point) := by
    have termIdentity (shift : ℤ) : pairTerm (cellConvolutionEquiv (target, shift)) =
        ((seedInverseCells parameter shift).comp (seedMatrixCells parameter (target - shift)))
          ((field.1 (cell - target)).value point) := by
      have indexIdentity : cell - shift - (target - shift) = cell - target := by ring
      show seedInverseCells parameter shift (seedMatrixCells parameter (target - shift)
        ((field.1 (cell - shift - (target - shift))).value point)) = _
      rw [indexIdentity, ContinuousLinearMap.comp_apply]
    rw [tsum_congr termIdentity]
    exact ((ContinuousLinearMap.apply ℂ (ComplexEuclidean 2)
      ((field.1 (cell - target)).value point)).map_tsum (convSummable target)).symm
  have deltaCollapse (target : ℤ) : (∑' shift, (seedInverseCells parameter shift).comp
      (seedMatrixCells parameter (target - shift))) ((field.1 (cell - target)).value point) =
      if target = 0 then ((field.1 cell).value point) else 0 := by
    rw [convDelta target]
    by_cases zeroTarget : target = 0
    · rw [if_pos zeroTarget, if_pos zeroTarget, zeroTarget, sub_zero,
        ContinuousLinearMap.id_apply]
    · rw [if_neg zeroTarget, if_neg zeroTarget]
      rfl
  have deltaSum : (∑' target : ℤ, if target = 0 then ((field.1 cell).value point) else 0) =
      (field.1 cell).value point := tsum_ite_eq 0 _
  rw [leftIterated, pairIdentity, tsum_congr innerCollapse, tsum_congr deltaCollapse, deltaSum]

end Grad.Constraints.Gauges
