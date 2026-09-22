import GaugeConvolutionFourier
import Mathlib.Analysis.Fourier.AddCircle

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators Matrix

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Frame

local instance gaugePeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem harmonicSeedOperator_entry (parameter : Seed.Parameters) (angle : ℝ)
    (row column : Fin 2) :
    operatorEntry (harmonicSeedOperator (parameter 0) (parameter 1) (parameter 2)
        (parameter 3) angle) row column =
      (Seed.actualMatrix parameter angle row column : ℂ) := by
  unfold operatorEntry harmonicSeedOperator
  rw [Grad.GaugeCoefficients.Physical.matrixEmbedding_apply, Fin.sum_univ_two,
    planarBasis_apply, planarBasis_apply]
  fin_cases column <;>
    simp [Seed.actualMatrix]

theorem transposeOperator_comp_trace (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) :
    operatorTrace ((transposeOperator mapping).comp mapping) =
      operatorEntry mapping 0 0 ^ 2 + operatorEntry mapping 1 0 ^ 2 +
        operatorEntry mapping 0 1 ^ 2 + operatorEntry mapping 1 1 ^ 2 := by
  unfold operatorTrace
  rw [operatorEntry_comp, operatorEntry_comp, transposeOperator_entry,
    transposeOperator_entry, transposeOperator_entry, transposeOperator_entry]
  ring

theorem seedMatrix_trace_pointwise (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (angle : ℝ) :
    operatorTrace ((transposeOperator (harmonicSeedOperator (parameter 0) (parameter 1)
        (parameter 2) (parameter 3) angle)).comp
      (harmonicSeedOperator (parameter 0) (parameter 1) (parameter 2) (parameter 3) angle)) =
      2 := by
  have algebra := (Seed.actualSeedAlgebra parameter inside angle).1
  have expand : ((Seed.actualMatrix parameter angle)ᵀ * Seed.actualMatrix parameter angle).trace =
      Seed.actualMatrix parameter angle 0 0 ^ 2 + Seed.actualMatrix parameter angle 1 0 ^ 2 +
        Seed.actualMatrix parameter angle 0 1 ^ 2 + Seed.actualMatrix parameter angle 1 1 ^ 2 := by
    rw [Matrix.trace_fin_two]
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.transpose_apply, Fin.sum_univ_two]
    ring
  rw [expand] at algebra
  rw [transposeOperator_comp_trace, harmonicSeedOperator_entry, harmonicSeedOperator_entry,
    harmonicSeedOperator_entry, harmonicSeedOperator_entry]
  exact_mod_cast congrArg (fun value : ℝ => (value : ℂ)) algebra

/-- Norm-summability of the full seed coefficient families. -/
theorem seedMatrixCells_norm_summable (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) :
    Summable (fun cell => ‖seedMatrixCells parameter cell‖) :=
  coefficientNorm_summable phase _ (seedMatrixCells_envelope_summable phase parameter inside 0)

theorem seedTransposeCells_norm_summable (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) :
    Summable (fun cell => ‖seedTransposeCells parameter cell‖) :=
  coefficientNorm_summable phase _
    (seedTransposeCells_envelope_summable phase parameter inside 0)

theorem seedInverseCells_norm_summable (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) :
    Summable (fun cell => ‖seedInverseCells parameter cell‖) :=
  coefficientNorm_summable phase _ (seedInverseCells_envelope_summable phase parameter inside 0)

/-- The convolution of two norm-summable families has summable norm rows and a
summable total row family. -/
theorem convolution_norm_rows
    (firstCoefficients secondCoefficients : ℤ → ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (firstSummable : Summable (fun cell => ‖firstCoefficients cell‖))
    (secondSummable : Summable (fun cell => ‖secondCoefficients cell‖)) :
    (∀ target : ℤ, Summable (fun shift =>
      ‖firstCoefficients shift‖ * ‖secondCoefficients (target - shift)‖)) ∧
    Summable (fun target : ℤ => ∑' shift,
      ‖firstCoefficients shift‖ * ‖secondCoefficients (target - shift)‖) := by
  have pairProduct : Summable (fun pair : ℤ × ℤ =>
      ‖firstCoefficients pair.1‖ * ‖secondCoefficients pair.2‖) :=
    firstSummable.mul_of_nonneg secondSummable (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have reindexed : Summable (fun pair : ℤ × ℤ =>
      ‖firstCoefficients (cellConvolutionEquiv pair).1‖ *
        ‖secondCoefficients (cellConvolutionEquiv pair).2‖) :=
    cellConvolutionEquiv.summable_iff.mpr pairProduct
  have nonnegative : ∀ pair : ℤ × ℤ,
      0 ≤ ‖firstCoefficients (cellConvolutionEquiv pair).1‖ *
        ‖secondCoefficients (cellConvolutionEquiv pair).2‖ :=
    fun pair => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have split := (summable_prod_of_nonneg nonnegative).mp reindexed
  exact ⟨fun target => split.1 target, split.2⟩

/-- Exact delta law for the trace convolution of the transposed and plain full
seed matrix families: the literal N11 trace normalization at every Fourier
output. -/
theorem seedTrace_delta (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) :
    (∀ target : ℤ, Summable (fun shift => operatorTrace
      ((seedTransposeCells parameter shift).comp
        (seedMatrixCells parameter (target - shift))))) ∧
    ∀ target : ℤ, (∑' shift, operatorTrace
        ((seedTransposeCells parameter shift).comp
          (seedMatrixCells parameter (target - shift)))) =
      if target = 0 then 2 else 0 := by
  have firstNorms := seedTransposeCells_norm_summable phase parameter inside
  have secondNorms := seedMatrixCells_norm_summable phase parameter inside
  obtain ⟨rowNorms, totalNorms⟩ := convolution_norm_rows _ _ firstNorms secondNorms
  have traceRowBound (target shift : ℤ) : ‖operatorTrace
      ((seedTransposeCells parameter shift).comp
        (seedMatrixCells parameter (target - shift)))‖ ≤
      2 * (‖seedTransposeCells parameter shift‖ *
        ‖seedMatrixCells parameter (target - shift)‖) :=
    operatorTrace_comp_norm_le _ _
  have traceSummable (target : ℤ) : Summable (fun shift => operatorTrace
      ((seedTransposeCells parameter shift).comp
        (seedMatrixCells parameter (target - shift)))) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (traceRowBound target) ((rowNorms target).mul_left 2))
  refine ⟨traceSummable, ?_⟩
  set traceRow : ℤ → ℂ := fun target => ∑' shift, operatorTrace
    ((seedTransposeCells parameter shift).comp
      (seedMatrixCells parameter (target - shift))) with traceRow_def
  set deltaRow : ℤ → ℂ := fun target => if target = 0 then 2 else 0 with deltaRow_def
  have traceRowNormBound (target : ℤ) : ‖traceRow target‖ ≤
      2 * ∑' shift, ‖seedTransposeCells parameter shift‖ *
        ‖seedMatrixCells parameter (target - shift)‖ := by
    calc ‖traceRow target‖
        ≤ ∑' shift, ‖operatorTrace ((seedTransposeCells parameter shift).comp
            (seedMatrixCells parameter (target - shift)))‖ :=
          norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
            (traceRowBound target) ((rowNorms target).mul_left 2))
      _ ≤ ∑' shift, 2 * (‖seedTransposeCells parameter shift‖ *
            ‖seedMatrixCells parameter (target - shift)‖) :=
          (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
            (traceRowBound target) ((rowNorms target).mul_left 2)).tsum_le_tsum
            (traceRowBound target) ((rowNorms target).mul_left 2)
      _ = 2 * ∑' shift, ‖seedTransposeCells parameter shift‖ *
            ‖seedMatrixCells parameter (target - shift)‖ := tsum_mul_left
  have traceRowNormSummable : Summable (fun target => ‖traceRow target‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) traceRowNormBound
      (totalNorms.mul_left 2)
  have deltaRowNormSummable : Summable (fun target => ‖deltaRow target‖) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro target outside
    have nonzero : target ≠ 0 := by simpa using outside
    rw [deltaRow_def]
    simp [nonzero]
  have differenceNorms : Summable (fun target => ‖traceRow target - deltaRow target‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun target => norm_sub_le _ _) (traceRowNormSummable.add deltaRowNormSummable)
  have convSummable (target : ℤ) : Summable (fun shift =>
      (seedTransposeCells parameter shift).comp
        (seedMatrixCells parameter (target - shift))) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun shift => ContinuousLinearMap.opNorm_comp_le _ _) (rowNorms target))
  have convNormBound (target : ℤ) : ‖∑' shift, (seedTransposeCells parameter shift).comp
      (seedMatrixCells parameter (target - shift))‖ ≤
      ∑' shift, ‖seedTransposeCells parameter shift‖ *
        ‖seedMatrixCells parameter (target - shift)‖ :=
    (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun shift => ContinuousLinearMap.opNorm_comp_le _ _) (rowNorms target))).trans
      ((Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun shift => ContinuousLinearMap.opNorm_comp_le _ _)
        (rowNorms target)).tsum_le_tsum
          (fun shift => ContinuousLinearMap.opNorm_comp_le _ _) (rowNorms target))
  have phasedConvSummable (angle : ℝ) : Summable (fun target : ℤ =>
      fourierPhase target angle • ∑' shift, (seedTransposeCells parameter shift).comp
        (seedMatrixCells parameter (target - shift))) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun target => ?_) totalNorms
    rw [norm_smul, fourierPhase_norm, one_mul]
    exact convNormBound target
  have realSumIdentity (angle : ℝ) : (∑' target : ℤ,
      fourierPhase target angle • traceRow target) = 2 := by
    have traceConv (target : ℤ) : traceRow target = operatorTrace (∑' shift,
        (seedTransposeCells parameter shift).comp
          (seedMatrixCells parameter (target - shift))) := by
      rw [traceRow_def]
      have mapped := operatorTraceContinuous.map_tsum (convSummable target)
      simp only [operatorTraceContinuous_apply] at mapped
      exact mapped.symm
    have phasedTrace (target : ℤ) : fourierPhase target angle • traceRow target =
        operatorTrace (fourierPhase target angle • ∑' shift,
          (seedTransposeCells parameter shift).comp
            (seedMatrixCells parameter (target - shift))) := by
      rw [traceConv, ← operatorTraceContinuous_apply, ← map_smul,
        operatorTraceContinuous_apply]
    rw [tsum_congr phasedTrace]
    have pulled := operatorTraceContinuous.map_tsum (phasedConvSummable angle)
    simp only [operatorTraceContinuous_apply] at pulled
    rw [← pulled, operatorComposeConvolution_fourier _ _ firstNorms secondNorms angle,
      seedTransposeCells_fourier phase parameter inside angle,
      seedMatrixCells_fourier phase parameter inside angle]
    exact seedMatrix_trace_pointwise parameter inside angle
  have deltaSumIdentity (angle : ℝ) : (∑' target : ℤ,
      fourierPhase target angle • deltaRow target) = 2 := by
    have pointTerm (target : ℤ) : fourierPhase target angle • deltaRow target =
        if target = 0 then (2 : ℂ) else 0 := by
      show fourierPhase target angle • (if target = 0 then (2 : ℂ) else 0) =
        if target = 0 then (2 : ℂ) else 0
      by_cases zeroTarget : target = 0
      · rw [if_pos zeroTarget, zeroTarget, fourierPhase_zero, one_smul]
      · rw [if_neg zeroTarget, smul_eq_mul, mul_zero]
    rw [tsum_congr pointTerm, tsum_ite_eq]
  have traceSummableComplex : Summable (fun target => traceRow target) :=
    traceRowNormSummable.of_norm
  have deltaSummableComplex : Summable (fun target => deltaRow target) :=
    deltaRowNormSummable.of_norm
  have circleSumZero : ∀ circle : CellCircle, (∑' target : ℤ,
      cellCharacter target circle • (traceRow target - deltaRow target)) = 0 := by
    intro circle
    induction circle using QuotientAddGroup.induction_on with
    | H angle =>
      have termIdentity (target : ℤ) : cellCharacter target (angle : CellCircle) •
          (traceRow target - deltaRow target) =
          fourierPhase target angle • traceRow target -
            fourierPhase target angle • deltaRow target := by
        rw [cellCharacter_coe, smul_sub]
        rfl
      rw [tsum_congr termIdentity]
      have traceSide : Summable (fun target => fourierPhase target angle • traceRow target) := by
        apply Summable.of_norm
        simpa only [norm_smul, fourierPhase_norm, one_mul] using traceRowNormSummable
      have deltaSide : Summable (fun target => fourierPhase target angle • deltaRow target) := by
        apply Summable.of_norm
        simpa only [norm_smul, fourierPhase_norm, one_mul] using deltaRowNormSummable
      rw [traceSide.tsum_sub deltaSide, realSumIdentity angle, deltaSumIdentity angle,
        sub_self]
  intro target
  have recovered := seedCircleSeries_coefficient
    (fun index => traceRow index - deltaRow index) differenceNorms target
  have zeroFunction : (fun circle : CellCircle => ∑' index : ℤ,
      cellCharacter index circle • (traceRow index - deltaRow index)) =
      fun _ : CellCircle => (0 : ℂ) := funext circleSumZero
  rw [zeroFunction] at recovered
  have zeroCoefficient : fourierCoeff (T := 2 * Real.pi)
      (fun _ : CellCircle => (0 : ℂ)) target = 0 := by
    unfold fourierCoeff
    simp
  rw [zeroCoefficient] at recovered
  have equal := sub_eq_zero.mp recovered.symm
  rw [traceRow_def, deltaRow_def] at equal
  simpa using equal

end Grad.Constraints.Gauges
