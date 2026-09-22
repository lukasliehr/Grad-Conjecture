import BCT8ActualBoundaryKernels
import BKB33FixedFourierKernels

noncomputable section

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.PhaseAlgebra

/-- The literal high angular projector, preserving every axial Fourier cell. -/
def highAngularMultiplier (mode : ℤ × ℤ) : ℂ :=
  if 3 ≤ |mode.1| then 1 else 0

theorem highAngularMultiplier_norm_le (mode : ℤ × ℤ) :
    ‖highAngularMultiplier mode‖ ≤ 1 := by
  unfold highAngularMultiplier
  split <;> simp

def highAngularKernel (parameters : PhaseParameters) (dimension : ℕ) :
    FullTwoFrequencyKernel parameters dimension dimension :=
  scalarModeDiagonalKernel parameters dimension highAngularMultiplier 1
    highAngularMultiplier_norm_le

/-- A diagonal multiplier has no tangential displacement cost. The fixed
phase comparison constant is independent of the running grade. -/
theorem modeDiagonalKernel_moment_bound (parameters : PhaseParameters)
    (input output moment : ℕ)
    (diagonal : (ℤ × ℤ) → (ComplexEuclidean input →L[ℂ] ComplexEuclidean output))
    (bound : ℝ) (bounded : ∀ mode, ‖diagonal mode‖ ≤ bound) :
    fullKernelMoment parameters moment
      (modeDiagonalKernel parameters input output diagonal bound bounded) ≤
      Real.exp (parameters.sigma0 + parameters.gamma) * bound := by
  let kernel := modeDiagonalKernel parameters input output diagonal bound bounded
  have envelope : ∀ shift, kernel.entryNorm shift ≤
      if shift = (0, 0) then bound else 0 := by
    intro shift
    exact fullKernelOfEntries_entryNorm_le parameters _ _ _ _ shift
  unfold fullKernelMoment
  apply ((kernel.moments moment).tsum_le_tsum
    (fun shift => mul_le_mul_of_nonneg_left (envelope shift)
      (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters shift)
        (pow_nonneg (annularFrequency_pos shift).le moment)))
    (modeDiagonalMajorant_moments parameters bound moment)).trans_eq
  rw [tsum_eq_single (0, 0) (by
    intro shift nonzero
    simp only [if_neg nonzero, mul_zero])]
  simp [boundaryCoefficientPhaseCost, phaseWeight, annularFrequency]

theorem scalarModeDiagonalKernel_moment_bound (parameters : PhaseParameters)
    (dimension moment : ℕ) (multiplier : ℤ × ℤ → ℂ) (bound : ℝ)
    (bounded : ∀ input, ‖multiplier input‖ ≤ bound) :
    fullKernelMoment parameters moment
      (scalarModeDiagonalKernel parameters dimension multiplier bound bounded) ≤
      Real.exp (parameters.sigma0 + parameters.gamma) * bound :=
  modeDiagonalKernel_moment_bound parameters dimension dimension moment _ bound _

theorem highAngularKernel_moment_bound (parameters : PhaseParameters)
    (dimension moment : ℕ) :
    fullKernelMoment parameters moment (highAngularKernel parameters dimension) ≤
      Real.exp (parameters.sigma0 + parameters.gamma) := by
  simpa only [highAngularKernel, mul_one] using scalarModeDiagonalKernel_moment_bound parameters
    dimension moment highAngularMultiplier 1 highAngularMultiplier_norm_le

end Grad.ActualBoundaryPrimitives
