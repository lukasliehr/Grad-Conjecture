import AHW9CompletedEliminatedXAction

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.SourceCollarCoefficients Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives
open Grad.GaugeCoefficients.Physical.Allocation

/-- The three literal Fourier operations: identity, R, and axial derivative. -/
def cofactorJetMultiplier (direction : Fin 3) (mode : ℤ × ℤ) : ℂ :=
  if direction = 0 then 1 else Complex.I * (if direction = 1 then (mode.1 : ℂ) else (mode.2 : ℂ))

theorem cofactorJetMultiplier_norm (direction : Fin 3) (mode : ℤ × ℤ) :
    ‖cofactorJetMultiplier direction mode‖ ≤ annularFrequency mode.1 mode.2 := by
  have first : ‖(mode.1 : ℂ)‖ = |(mode.1 : ℝ)| := by norm_cast
  have second : ‖(mode.2 : ℂ)‖ = |(mode.2 : ℝ)| := by norm_cast
  fin_cases direction
  · change ‖(1 : ℂ)‖ ≤ _
    rw [norm_one]
    unfold annularFrequency
    linarith [abs_nonneg (mode.1 : ℝ), abs_nonneg (mode.2 : ℝ)]
  · change ‖Complex.I * (mode.1 : ℂ)‖ ≤ _
    rw [norm_mul, Complex.norm_I, one_mul, first]
    unfold annularFrequency
    linarith [abs_nonneg (mode.2 : ℝ)]
  · change ‖Complex.I * (mode.2 : ℂ)‖ ≤ _
    rw [norm_mul, Complex.norm_I, one_mul, second]
    unfold annularFrequency
    linarith [abs_nonneg (mode.1 : ℝ)]

def cofactorJetSequence (direction : Fin 3) (sequence : ℤ × ℤ → ℂ) (mode : ℤ × ℤ) : ℂ :=
  cofactorJetMultiplier direction mode * sequence mode

theorem cofactorJetSequence_moment_le (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (direction : Fin 3) (sequence : ℤ × ℤ → ℂ) (mode : ℤ × ℤ) :
    productMoment parameters power radius (cofactorJetSequence direction sequence) mode ≤
      productMoment parameters (power + 1) radius sequence mode := by
  unfold productMoment cofactorJetSequence
  rw [norm_mul, pow_succ]
  have bound := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (cofactorJetMultiplier_norm direction mode) (norm_nonneg (sequence mode)))
    (mul_nonneg (coefficientRadialEnvelope_pos parameters mode.2 radius).le
      (pow_nonneg (annularFrequency_nonnegative mode.1 mode.2) power))
  exact bound.trans_eq (by ring)

theorem cofactorJetSequence_moment_summable (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (direction : Fin 3) (sequence : ℤ × ℤ → ℂ)
    (summable : Summable (productMoment parameters (power + 1) radius sequence)) :
    Summable (productMoment parameters power radius (cofactorJetSequence direction sequence)) :=
  Summable.of_nonneg_of_le (productMoment_nonnegative _ _ _ _)
    (cofactorJetSequence_moment_le parameters power radius direction sequence) summable

/-- Actual signed cofactor deviation rows, including the previously unextracted rho row. -/
def radialCofactorJetScalar (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row column : Fin 3)
    (radial : Fin 2) (direction : Fin 3) (r : RadialPoint) : ℤ × ℤ → ℂ :=
  cofactorJetSequence direction (polarEntryScalar parameters
    (originalCofactorDeviation parameters L state.val.val.epsilon state.val.val.field)
    (originalCofactorDeviation_coherent parameters L state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low)
    row column radial.val r.val)

theorem radialCofactorJetScalar_moments (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row column : Fin 3)
    (radial : Fin 2) (direction : Fin 3) (r : RadialPoint) (moment : ℕ) :
    Summable (productMoment parameters moment r.val (radialCofactorJetScalar parameters L compact state row column radial direction r)) :=
  cofactorJetSequence_moment_summable parameters moment r.val direction _
    (polarEntryScalarMoment_summable parameters _ _ row column (moment + 1) radial.val r.val r.property.1 r.property.2)

def cofactorJetConstant (parameters : PhaseParameters) (L : ℝ) (row column : Fin 3)
    (radial : Fin 2) (moment : ℕ) : ℝ :=
  physicalPolarEntryConstant (originalCofactorProfile parameters L).deviation row column (moment + 1) radial.val

theorem cofactorJetConstant_nonnegative (parameters : PhaseParameters) (L : ℝ) (row column : Fin 3)
    (radial : Fin 2) (moment : ℕ) : 0 ≤ cofactorJetConstant parameters L row column radial moment :=
  physicalPolarEntryConstant_nonnegative _ _ _ _ _

/-- Two displayed derivatives fit the same original B_(moment+7), with no extra low ball. -/
theorem radialCofactorJetScalar_moment_bound (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row column : Fin 3)
    (radial : Fin 2) (direction : Fin 3) (r : RadialPoint) (moment : ℕ) :
    (∑' mode, productMoment parameters moment r.val (radialCofactorJetScalar parameters L compact state row column radial direction r) mode) ≤
      cofactorJetConstant parameters L row column radial moment * state.val.errorBudget moment := by
  have sourceSummable := polarEntryScalarMoment_summable parameters
    (originalCofactorDeviation parameters L state.val.val.epsilon state.val.val.field)
    (originalCofactorDeviation_coherent parameters L state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low)
    row column (moment + 1) radial.val r.val r.property.1 r.property.2
  apply ((radialCofactorJetScalar_moments parameters L compact state row column radial direction r moment).tsum_le_tsum
    (cofactorJetSequence_moment_le parameters moment r.val direction _) sourceSummable).trans
  apply (physicalPolarEntryScalarMoment_bound parameters _ _ state.val.val.field state.val.val.rho state.val.val.epsilon
    (originalCofactorProfile parameters L).deviation
    (originalCofactorDeviation_bound parameters L state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low)
    row column (moment + 1) radial.val r.val r.property.1 r.property.2).trans
  apply mul_le_mul_of_nonneg_left _ (cofactorJetConstant_nonnegative parameters L row column radial moment)
  exact physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon (by omega)

theorem radialCofactorJetScalar_continuous (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row column : Fin 3)
    (radial : Fin 2) (direction : Fin 3) (mode : ℤ × ℤ) :
    Continuous (fun r : RadialPoint => radialCofactorJetScalar parameters L compact state row column radial direction r mode) := by
  apply continuous_const.mul
  exact (continuous_iff_continuousAt.mpr (fun radius =>
    (polarEntryScalar_hasDerivAt parameters _ _ row column radial.val radius mode).continuousAt)).comp continuous_subtype_val

end Grad.AnnularReconstruction
