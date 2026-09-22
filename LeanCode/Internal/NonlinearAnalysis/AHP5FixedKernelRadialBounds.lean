import AHP4ActualRadialGaugeSigmaKernels

noncomputable section
set_option maxHeartbeats 1200000

namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.SourceCollarCoefficients Grad.PhaseAlgebra

/-- Exact equality of entries across the bookkeeping phase parameter.
This relation never changes a physical coefficient. -/
def SameKernelEntries {input output : ℕ} {first second : PhaseParameters}
    (left : FullTwoFrequencyKernel first input output)
    (right : FullTwoFrequencyKernel second input output) : Prop :=
  ∀ shift mode, left.entry shift mode = right.entry shift mode

theorem SameKernelEntries.entryNorm {input output : ℕ} {first second : PhaseParameters}
    {left : FullTwoFrequencyKernel first input output}
    {right : FullTwoFrequencyKernel second input output}
    (same : SameKernelEntries left right) (shift : ℤ × ℤ) :
    left.entryNorm shift = right.entryNorm shift := by
  apply le_antisymm
  · apply left.entryNorm_le
    intro mode
    rw [same shift mode]
    exact right.entry_le shift mode
  · apply right.entryNorm_le
    intro mode
    rw [← same shift mode]
    exact left.entry_le shift mode

theorem SameKernelEntries.add {input output : ℕ} {first second : PhaseParameters}
    {left₁ left₂ : FullTwoFrequencyKernel first input output}
    {right₁ right₂ : FullTwoFrequencyKernel second input output}
    (one : SameKernelEntries left₁ right₁) (two : SameKernelEntries left₂ right₂) :
    SameKernelEntries (fullKernelAdd left₁ left₂) (fullKernelAdd right₁ right₂) := by
  intro shift mode
  simp only [fullKernelAdd_entry, one shift mode, two shift mode]

theorem SameKernelEntries.comp {input middle output : ℕ} {first second : PhaseParameters}
    {left₁ : FullTwoFrequencyKernel first middle output}
    {left₂ : FullTwoFrequencyKernel first input middle}
    {right₁ : FullTwoFrequencyKernel second middle output}
    {right₂ : FullTwoFrequencyKernel second input middle}
    (one : SameKernelEntries left₁ right₁) (two : SameKernelEntries left₂ right₂) :
    SameKernelEntries (fullKernelComposition left₁ left₂)
      (fullKernelComposition right₁ right₂) := by
  intro shift mode
  rw [fullKernelComposition_entry, fullKernelComposition_entry]
  apply tsum_congr
  intro middle
  rw [one (shift - middle) (mode + middle), two middle mode]

/-- The fixed upper bookkeeping phase is used only to choose constants.
Actual radius kernels retain their exact original radial envelope. -/
abbrev maximalKernelParameters (parameters : PhaseParameters) : PhaseParameters :=
  radialKernelParameters parameters ⟨0, le_rfl, zero_le_one⟩

theorem radialKernelPhaseCost_le_maximal (parameters : PhaseParameters)
    (r : RadialPoint) (shift : ℤ × ℤ) :
    boundaryCoefficientPhaseCost (radialKernelParameters parameters r) shift ≤
      boundaryCoefficientPhaseCost (maximalKernelParameters parameters) shift := by
  rw [radialKernelPhaseCost, radialKernelPhaseCost]
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    have := mul_nonneg parameters.gamma_pos.le r.property.1
    dsimp only
    nlinarith
  · unfold coefficientRadialEnvelope
    apply Real.exp_le_exp.mpr
    have := mul_nonneg (mul_nonneg parameters.gamma_pos.le r.property.1)
      (abs_nonneg (shift.2 : ℝ))
    dsimp only
    nlinarith
  · exact (coefficientRadialEnvelope_pos parameters shift.2 r.val).le
  · exact (Real.exp_pos _).le

theorem SameKernelEntries.radialMoment_le {input output : ℕ}
    (parameters : PhaseParameters) (r : RadialPoint) (moment : ℕ)
    {left : RadialKernel parameters r input output}
    {right : FullTwoFrequencyKernel (maximalKernelParameters parameters) input output}
    (same : SameKernelEntries left right) :
    fullKernelMoment (radialKernelParameters parameters r) moment left ≤
      fullKernelMoment (maximalKernelParameters parameters) moment right := by
  apply (left.moments moment).tsum_le_tsum _ (right.moments moment)
  intro shift
  rw [same.entryNorm shift]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (radialKernelPhaseCost_le_maximal parameters r shift)
      (pow_nonneg (annularFrequency_pos shift).le _))
    (fullKernelEntryNorm_nonnegative right shift)

theorem sameConstantMatrixKernel (first second : PhaseParameters)
    (input output : ℕ)
    (mapping : Grad.ClosedJets.ComplexEuclidean input →L[ℂ]
      Grad.ClosedJets.ComplexEuclidean output) :
    SameKernelEntries (constantMatrixKernel first input output mapping)
      (constantMatrixKernel second input output mapping) := by
  intro shift mode
  rfl

theorem sameScalarModeDiagonalKernel (first second : PhaseParameters)
    (dimension : ℕ) (multiplier : ℤ × ℤ → ℂ) (bound : ℝ)
    (bounded : ∀ mode, ‖multiplier mode‖ ≤ bound) :
    SameKernelEntries (scalarModeDiagonalKernel first dimension multiplier bound bounded)
      (scalarModeDiagonalKernel second dimension multiplier bound bounded) := by
  intro shift mode
  rfl

theorem sameComponentModeKernel (first second : PhaseParameters)
    (dimension : ℕ) (component : Fin dimension)
    (multiplier : ℤ × ℤ → ℂ) (bound : ℝ)
    (bounded : ∀ mode, ‖multiplier mode‖ ≤ bound) :
    SameKernelEntries (componentModeKernel first dimension component multiplier bound bounded)
      (componentModeKernel second dimension component multiplier bound bounded) := by
  unfold componentModeKernel coordinateInjectionKernel coordinateProjectionKernel
  exact (sameConstantMatrixKernel first second _ _ _).comp
    ((sameScalarModeDiagonalKernel first second _ _ _ _).comp
      (sameConstantMatrixKernel first second _ _ _))

theorem sameEncodedJKernel (first second : PhaseParameters) :
    SameKernelEntries (encodedJKernel first) (encodedJKernel second) := by
  unfold encodedJKernel angularMeanComponentKernel angularDoubleInverseComponentKernel
    angularInverseComponentKernel
  exact (sameComponentModeKernel first second _ _ _ _ _).add
    ((sameComponentModeKernel first second _ _ _ _ _).add
      (sameComponentModeKernel first second _ _ _ _ _))

theorem sameEncodedRotationKernel (first second : PhaseParameters) :
    SameKernelEntries (encodedRotationKernel first) (encodedRotationKernel second) := by
  unfold encodedRotationKernel angularMeanFreeComponentKernel angularInverseComponentKernel
  exact (sameComponentModeKernel first second _ _ _ _ _).add
    (sameComponentModeKernel first second _ _ _ _ _)

end Grad.AnnularReconstruction
