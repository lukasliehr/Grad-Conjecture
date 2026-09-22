import GaugeSeedFamilies

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Frame

theorem cellExponential_eq_fourierPhase :
    Grad.CartesianState.cellExponential = fourierPhase := rfl

theorem fourierPhase_zero (angle : ℝ) : fourierPhase 0 angle = 1 := by
  unfold fourierPhase
  norm_num

theorem transposeOperator_id :
    transposeOperator (ContinuousLinearMap.id ℂ (ComplexEuclidean 2)) =
      ContinuousLinearMap.id ℂ (ComplexEuclidean 2) := by
  apply ContinuousLinearMap.ext
  intro value
  rw [transposeOperator_apply]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [operatorEntry, planarBasis_apply]

/-- Absolutely convergent operator-operator Fourier convolution identity. -/
theorem operatorComposeConvolution_fourier
    (firstCoefficients secondCoefficients : ℤ → ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (firstSummable : Summable (fun cell => ‖firstCoefficients cell‖))
    (secondSummable : Summable (fun cell => ‖secondCoefficients cell‖)) (angle : ℝ) :
    (∑' cell : ℤ, fourierPhase cell angle •
      ∑' shift : ℤ, (firstCoefficients shift).comp (secondCoefficients (cell - shift))) =
      ((∑' shift : ℤ, fourierPhase shift angle • firstCoefficients shift).comp
        (∑' cell : ℤ, fourierPhase cell angle • secondCoefficients cell)) := by
  let pairTerm (pair : ℤ × ℤ) :=
    (fourierPhase pair.1 angle • firstCoefficients pair.1).comp
      (fourierPhase pair.2 angle • secondCoefficients pair.2)
  have pairMajorant : Summable (fun pair : ℤ × ℤ =>
      ‖firstCoefficients pair.1‖ * ‖secondCoefficients pair.2‖) :=
    firstSummable.mul_of_nonneg secondSummable (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have pairNorm : Summable (fun pair => ‖pairTerm pair‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ pairMajorant
    intro pair
    calc ‖pairTerm pair‖
        ≤ ‖fourierPhase pair.1 angle • firstCoefficients pair.1‖ *
            ‖fourierPhase pair.2 angle • secondCoefficients pair.2‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖firstCoefficients pair.1‖ * ‖secondCoefficients pair.2‖ := by
          rw [norm_smul, norm_smul, fourierPhase_norm, fourierPhase_norm, one_mul, one_mul]
  have pairSum : Summable pairTerm := pairNorm.of_norm
  have reindexed : Summable (fun pair : ℤ × ℤ => pairTerm (cellConvolutionEquiv pair)) :=
    cellConvolutionEquiv.summable_iff.mpr pairSum
  have innerSummable (cell : ℤ) : Summable (fun shift =>
      (firstCoefficients shift).comp (secondCoefficients (cell - shift))) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun shift =>
      ContinuousLinearMap.opNorm_comp_le _ _)
    have secondBound (shift : ℤ) : ‖secondCoefficients (cell - shift)‖ ≤
        ∑' index, ‖secondCoefficients index‖ :=
      secondSummable.le_tsum (cell - shift) (fun _ _ => norm_nonneg _)
    apply Summable.of_nonneg_of_le
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun shift => mul_le_mul_of_nonneg_left (secondBound shift) (norm_nonneg _))
      (firstSummable.mul_right _)
  have literal (cell shift : ℤ) :
      fourierPhase cell angle •
          (firstCoefficients shift).comp (secondCoefficients (cell - shift)) =
        pairTerm (cellConvolutionEquiv (cell, shift)) := by
    show fourierPhase cell angle • _ =
      (fourierPhase shift angle • firstCoefficients shift).comp
        (fourierPhase (cell - shift) angle • secondCoefficients (cell - shift))
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul,
      ← fourierPhase_add, add_sub_cancel]
  have secondPhaseNorm : Summable (fun cell =>
      ‖fourierPhase cell angle • secondCoefficients cell‖) := by
    simpa only [norm_smul, fourierPhase_norm, one_mul] using secondSummable
  have firstPhaseNorm : Summable (fun cell =>
      ‖fourierPhase cell angle • firstCoefficients cell‖) := by
    simpa only [norm_smul, fourierPhase_norm, one_mul] using firstSummable
  calc
    (∑' cell : ℤ, fourierPhase cell angle •
        ∑' shift : ℤ, (firstCoefficients shift).comp (secondCoefficients (cell - shift)))
      = ∑' cell : ℤ, ∑' shift : ℤ, pairTerm (cellConvolutionEquiv (cell, shift)) := by
        apply tsum_congr
        intro cell
        rw [← tsum_const_smul'']
        exact tsum_congr (literal cell)
    _ = ∑' pair : ℤ × ℤ, pairTerm (cellConvolutionEquiv pair) := reindexed.tsum_prod.symm
    _ = ∑' pair : ℤ × ℤ, pairTerm pair := cellConvolutionEquiv.tsum_eq pairTerm
    _ = ∑' shift : ℤ, ∑' cell : ℤ, pairTerm (shift, cell) := pairSum.tsum_prod
    _ = ∑' shift : ℤ, (fourierPhase shift angle • firstCoefficients shift).comp
        (∑' cell : ℤ, fourierPhase cell angle • secondCoefficients cell) := by
        apply tsum_congr
        intro shift
        exact ((ContinuousLinearMap.compL ℂ (ComplexEuclidean 2) (ComplexEuclidean 2)
          (ComplexEuclidean 2) (fourierPhase shift angle • firstCoefficients shift)).map_tsum
            secondPhaseNorm.of_norm).symm
    _ = _ := (((ContinuousLinearMap.compL ℂ (ComplexEuclidean 2) (ComplexEuclidean 2)
        (ComplexEuclidean 2)).flip
          (∑' cell : ℤ, fourierPhase cell angle • secondCoefficients cell)).map_tsum
            firstPhaseNorm.of_norm).symm

theorem delta_identity_fourier (angle : ℝ) :
    (∑' cell : ℤ, fourierPhase cell angle •
        (if cell = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0)) =
      ContinuousLinearMap.id ℂ (ComplexEuclidean 2) := by
  have pointTerm (cell : ℤ) : fourierPhase cell angle •
      (if cell = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0) =
      if cell = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0 := by
    by_cases zeroCell : cell = 0
    · rw [if_pos zeroCell, zeroCell, fourierPhase_zero, one_smul]
    · rw [if_neg zeroCell]
      exact smul_zero (A := ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
        (fourierPhase cell angle)
  rw [tsum_congr pointTerm, tsum_ite_eq]

theorem seedCells_value_norm_summable (phase : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain) (kind : Fin 3) :
    Summable (fun cell => ‖Seed.actualCells kind parameter cell‖) :=
  coefficientNorm_summable phase _ (seedCells_all_summable phase parameter inside kind 0)

theorem seedMatrixCells_fourier (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (angle : ℝ) :
    (∑' cell : ℤ, fourierPhase cell angle • seedMatrixCells parameter cell) =
      harmonicSeedOperator (parameter 0) (parameter 1) (parameter 2) (parameter 3) angle := by
  have deltaSummable : Summable (fun cell : ℤ => fourierPhase cell angle •
      (if cell = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0)) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro cell outside
    have nonzero : cell ≠ 0 := by simpa using outside
    rw [if_neg nonzero]
    exact smul_zero (A := ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
      (fourierPhase cell angle)
  have deviationSummable : Summable (fun cell : ℤ =>
      fourierPhase cell angle • Seed.actualCells 0 parameter cell) := by
    apply Summable.of_norm
    simpa only [norm_smul, fourierPhase_norm, one_mul] using
      seedCells_value_norm_summable phase parameter inside 0
  have expand : (fun cell : ℤ => fourierPhase cell angle • seedMatrixCells parameter cell) =
      fun cell : ℤ => fourierPhase cell angle •
          (if cell = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0) +
        fourierPhase cell angle • Seed.actualCells 0 parameter cell := by
    funext cell
    rw [seedMatrixCells, smul_add]
  rw [expand, deltaSummable.tsum_add deviationSummable, delta_identity_fourier]
  have deviation := (Seed.actual_seed_fourier phase parameter inside angle).1
  rw [cellExponential_eq_fourierPhase] at deviation
  rw [deviation]
  abel

theorem seedInverseCells_fourier (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (angle : ℝ) :
    (∑' cell : ℤ, fourierPhase cell angle • seedInverseCells parameter cell) =
      Seed.actualInverseOperator parameter angle := by
  have deltaSummable : Summable (fun cell : ℤ => fourierPhase cell angle •
      (if cell = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0)) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro cell outside
    have nonzero : cell ≠ 0 := by simpa using outside
    rw [if_neg nonzero]
    exact smul_zero (A := ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
      (fourierPhase cell angle)
  have deviationSummable : Summable (fun cell : ℤ =>
      fourierPhase cell angle • Seed.actualCells 1 parameter cell) := by
    apply Summable.of_norm
    simpa only [norm_smul, fourierPhase_norm, one_mul] using
      seedCells_value_norm_summable phase parameter inside 1
  have expand : (fun cell : ℤ => fourierPhase cell angle • seedInverseCells parameter cell) =
      fun cell : ℤ => fourierPhase cell angle •
          (if cell = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0) +
        fourierPhase cell angle • Seed.actualCells 1 parameter cell := by
    funext cell
    rw [seedInverseCells, smul_add]
  rw [expand, deltaSummable.tsum_add deviationSummable, delta_identity_fourier]
  have deviation := (Seed.actual_seed_fourier phase parameter inside angle).2.1
  rw [cellExponential_eq_fourierPhase] at deviation
  rw [deviation]
  abel

theorem seedTransposeCells_fourier (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (angle : ℝ) :
    (∑' cell : ℤ, fourierPhase cell angle • seedTransposeCells parameter cell) =
      transposeOperator
        (harmonicSeedOperator (parameter 0) (parameter 1) (parameter 2) (parameter 3) angle) := by
  have deltaSummable : Summable (fun cell : ℤ => fourierPhase cell angle •
      (if cell = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0)) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro cell outside
    have nonzero : cell ≠ 0 := by simpa using outside
    rw [if_neg nonzero]
    exact smul_zero (A := ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
      (fourierPhase cell angle)
  have deviationSummable : Summable (fun cell : ℤ =>
      fourierPhase cell angle • Seed.actualCells 0 parameter cell) := by
    apply Summable.of_norm
    simpa only [norm_smul, fourierPhase_norm, one_mul] using
      seedCells_value_norm_summable phase parameter inside 0
  have transposedSummable : Summable (fun cell : ℤ =>
      fourierPhase cell angle • transposeOperator (Seed.actualCells 0 parameter cell)) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun cell => ?_)
      ((seedCells_value_norm_summable phase parameter inside 0).mul_left 4)
    rw [norm_smul, fourierPhase_norm, one_mul]
    exact transposeOperator_norm_le _
  have expand : (fun cell : ℤ => fourierPhase cell angle • seedTransposeCells parameter cell) =
      fun cell : ℤ => fourierPhase cell angle •
          (if cell = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0) +
        fourierPhase cell angle • transposeOperator (Seed.actualCells 0 parameter cell) := by
    funext cell
    rw [seedTransposeCells, smul_add]
  rw [expand, deltaSummable.tsum_add transposedSummable, delta_identity_fourier]
  have transposedFactor : (∑' cell : ℤ, fourierPhase cell angle •
      transposeOperator (Seed.actualCells 0 parameter cell)) =
      transposeOperator (∑' cell : ℤ, fourierPhase cell angle •
        Seed.actualCells 0 parameter cell) := by
    have termEq (cell : ℤ) : fourierPhase cell angle •
        transposeOperator (Seed.actualCells 0 parameter cell) =
        transposeContinuous (fourierPhase cell angle • Seed.actualCells 0 parameter cell) := by
      rw [map_smul, transposeContinuous_apply]
    rw [tsum_congr termEq, ← transposeContinuous.map_tsum deviationSummable,
      transposeContinuous_apply]
  rw [transposedFactor]
  have deviation := (Seed.actual_seed_fourier phase parameter inside angle).1
  rw [cellExponential_eq_fourierPhase] at deviation
  have split : transposeOperator (harmonicSeedOperator (parameter 0) (parameter 1)
      (parameter 2) (parameter 3) angle - ContinuousLinearMap.id ℂ (ComplexEuclidean 2)) =
      transposeOperator (harmonicSeedOperator (parameter 0) (parameter 1)
        (parameter 2) (parameter 3) angle) -
        transposeOperator (ContinuousLinearMap.id ℂ (ComplexEuclidean 2)) :=
    transposeLinear.map_sub _ _
  rw [deviation, split, transposeOperator_id]
  abel

end Grad.Constraints.Gauges
