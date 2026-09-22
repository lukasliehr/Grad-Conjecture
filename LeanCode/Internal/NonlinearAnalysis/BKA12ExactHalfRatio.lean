import BKA11BoundaryKernelConsumer

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.PhaseAlgebra Grad.CartesianState

theorem boundaryCoefficientPhaseCost_formula (parameters : PhaseParameters)
    (shift : ℤ × ℤ) :
    boundaryCoefficientPhaseCost parameters shift =
      Real.exp (parameters.sigma0 + parameters.gamma) *
        Real.exp ((parameters.sigma0 - parameters.gamma) * |(shift.2 : ℝ)|) := by
  simp only [boundaryCoefficientPhaseCost, phaseWeight, phaseWidth, mul_one]

theorem negativeShiftCost_formula (parameters : PhaseParameters) (angular cell : ℕ)
    (shift : ℤ × ℤ) :
    negativeShiftCost parameters angular cell shift =
      Real.exp (parameters.sigma0 + parameters.gamma) *
        Real.exp ((parameters.sigma0 - parameters.gamma) * |(shift.2 : ℝ)|) *
          annularFrequency shift.1 shift.2 ^ (angular + cell + 1) := by
  simp only [negativeShiftCost, boundaryCoefficientPhaseCost, phaseWeight,
    phaseWidth, mul_one]

theorem finiteKernelMoment_formula {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension) :
    finiteKernelMoment parameters angular cell kernel =
      ∑ shift ∈ kernel.support,
        (Real.exp (parameters.sigma0 + parameters.gamma) *
          Real.exp ((parameters.sigma0 - parameters.gamma) * |(shift.2 : ℝ)|) *
            annularFrequency shift.1 shift.2 ^ (angular + cell + 1)) *
              ‖kernel shift‖ := by
  simp only [finiteKernelMoment, negativeShiftCost, boundaryCoefficientPhaseCost,
    phaseWeight, phaseWidth, mul_one]

theorem totalKernelMoment_formula {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (moment : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension) :
    totalKernelMoment parameters moment kernel =
      ∑ shift ∈ kernel.support,
        Real.exp (parameters.sigma0 + parameters.gamma) *
          Real.exp ((parameters.sigma0 - parameters.gamma) * |(shift.2 : ℝ)|) *
            annularFrequency shift.1 shift.2 ^ moment * ‖kernel shift‖ := by
  simp only [totalKernelMoment, boundaryCoefficientPhaseCost, phaseWeight,
    phaseWidth, mul_one]

/-- Literal AH17: the negative-half ratio costs exactly one half power of
the displacement frequency.  AH18 subsequently rounds this half moment up
to the integer moment already used by the finite-kernel action. -/
theorem negativeHalfRatio_le_sqrt_frequency (mode shift : ℤ × ℤ) :
    Real.sqrt (annularFrequency (mode.1 - shift.1) (mode.2 - shift.2) /
      annularFrequency mode.1 mode.2) ≤
        Real.sqrt (annularFrequency shift.1 shift.2) := by
  apply Real.sqrt_le_sqrt
  rw [div_le_iff₀ (annularFrequency_pos mode)]
  simpa only [mul_comm] using annularFrequency_sub_le_mul mode shift

/-- The exact half-order shift is available together with the complete
AH16--AH20 boundary-kernel consumer. -/
theorem ah17_exact_half_ratio_consumer (mode shift : ℤ × ℤ) :
    Real.sqrt (annularFrequency (mode.1 - shift.1) (mode.2 - shift.2) /
      annularFrequency mode.1 mode.2) ≤
        Real.sqrt (annularFrequency shift.1 shift.2) :=
  negativeHalfRatio_le_sqrt_frequency mode shift

end Grad.BoundaryKernelAction
