import AHP14ActualRadialCovariantReconstruction

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

theorem SameKernelEntries.neg {input output : ℕ} {first second : PhaseParameters}
    {left : FullTwoFrequencyKernel first input output}
    {right : FullTwoFrequencyKernel second input output}
    (same : SameKernelEntries left right) :
    SameKernelEntries (fullKernelNeg left) (fullKernelNeg right) := by
  intro shift mode
  rw [fullKernelNeg_entry, fullKernelNeg_entry, same shift mode]

theorem SameKernelEntries.sub {input output : ℕ} {first second : PhaseParameters}
    {left₁ left₂ : FullTwoFrequencyKernel first input output}
    {right₁ right₂ : FullTwoFrequencyKernel second input output}
    (one : SameKernelEntries left₁ right₁) (two : SameKernelEntries left₂ right₂) :
    SameKernelEntries (fullKernelSub left₁ left₂) (fullKernelSub right₁ right₂) :=
  one.add two.neg

theorem SameKernelEntries.smul {input output : ℕ} {first second : PhaseParameters}
    {left : FullTwoFrequencyKernel first input output}
    {right : FullTwoFrequencyKernel second input output}
    (same : SameKernelEntries left right) (scalar : ℂ) :
    SameKernelEntries (fullKernelSmul scalar left) (fullKernelSmul scalar right) := by
  intro shift mode
  rw [fullKernelSmul_entry, fullKernelSmul_entry, same shift mode]

theorem SameKernelEntries.power {dimension : ℕ} {first second : PhaseParameters}
    {left : FullTwoFrequencyKernel first dimension dimension}
    {right : FullTwoFrequencyKernel second dimension dimension}
    (same : SameKernelEntries left right) (exponent : ℕ) :
    SameKernelEntries (fullKernelPower left exponent) (fullKernelPower right exponent) := by
  induction exponent with
  | zero => exact same
  | succ n ih => exact ih.comp same

/-- The Neumann entries are independent of the chosen valid low-ball proof
and of the bookkeeping phase. The cached inverse algebra is reused. -/
theorem SameKernelEntries.negativeIdentityInverse {dimension : ℕ} {first second : PhaseParameters}
    {left : FullTwoFrequencyKernel first dimension dimension}
    {right : FullTwoFrequencyKernel second dimension dimension}
    (same : SameKernelEntries left right)
    (leftLow rightLow : ℝ)
    (leftBound : fullKernelMoment first 0 left ≤ leftLow)
    (rightBound : fullKernelMoment second 0 right ≤ rightLow)
    (leftSmall : leftLow < 1) (rightSmall : rightLow < 1) :
    SameKernelEntries (fullKernelNegativeIdentityInverse first left leftLow leftBound leftSmall)
      (fullKernelNegativeIdentityInverse second right rightLow rightBound rightSmall) := by
  intro shift mode
  simp only [fullKernelNegativeIdentityInverse, fullKernelNeumannSum,
    fullKernelNeg_entry, fullKernelAdd_entry, fullKernelNeumannTail_entry]
  rw [sameFullIdentityKernel first second dimension shift mode]
  congr 2
  apply tsum_congr
  intro exponent
  exact same.power exponent shift mode

abbrev outerRadialPoint : RadialPoint := ⟨1, zero_le_one, le_rfl⟩

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact)

/-- Exact coefficient identity for the two physical gauge rows, before inversion. -/
theorem radialGaugeRowsKernel_one :
    SameKernelEntries (radialGaugeRowsKernel parameters L compact state outerRadialPoint 0)
      (actualGaugeRowsKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon state.field state.coefficientSmall) := by
  intro shift mode
  rfl

theorem radialGammaDeviationKernel_one :
    SameKernelEntries (radialGammaDeviationKernel parameters L compact state outerRadialPoint)
      (actualGammaDeviationKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon state.field state.coefficientSmall) := by
  intro shift mode
  rfl

variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialGaugeLowRadius parameters L compact)

theorem radialNegativeGammaInverseKernel_one :
    SameKernelEntries
      (radialNegativeGammaInverseKernel parameters L compact state outerRadialPoint small)
      (actualNegativeGammaInverseKernelOnBall parameters L state.rho state.alpha state.delta
        state.parameter state.epsilon compact state.field state.gaugeSmall
        state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  unfold radialNegativeGammaInverseKernel actualNegativeGammaInverseKernelOnBall
    actualNegativeGammaInverseKernel
  exact ((radialGammaDeviationKernel_one parameters L compact state).neg).negativeIdentityInverse
    _ _ _ _ _ _

theorem radialGaugeMeanRowsKernel_one :
    SameKernelEntries (radialGaugeMeanRowsKernel parameters L compact state outerRadialPoint)
      (actualGaugeMeanRowsKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon state.field state.coefficientSmall) := by
  exact (sameScalarModeDiagonalKernel _ _ _ _ _ _).comp
    (radialGaugeRowsKernel_one parameters L compact state)

theorem radialGaugeCorrectionKernel_one :
    SameKernelEntries (radialGaugeCorrectionKernel parameters L compact state outerRadialPoint small)
      (actualGaugeCorrectionKernelOnBall parameters L state.rho state.alpha state.delta
        state.parameter state.epsilon compact state.field state.gaugeSmall
        state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  exact (sameConstantMatrixKernel _ _ _ _ _).comp
    ((radialNegativeGammaInverseKernel_one parameters L compact state small).comp
      (radialGaugeMeanRowsKernel_one parameters L compact state))

theorem radialGaugeQKernel_one :
    SameKernelEntries (radialGaugeQKernel parameters L compact state outerRadialPoint small)
      (actualGaugeQKernelOnBall parameters L state.rho state.alpha state.delta
        state.parameter state.epsilon compact state.field state.gaugeSmall
        state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  exact (sameFullIdentityKernel _ _ _).add
    (radialGaugeCorrectionKernel_one parameters L compact state small)

end Grad.AnnularReconstruction
