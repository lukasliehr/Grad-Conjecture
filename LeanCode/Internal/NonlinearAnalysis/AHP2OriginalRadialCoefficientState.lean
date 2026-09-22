import AHP1ExactRadialKernelPhase

noncomputable section

set_option maxHeartbeats 1200000

namespace Grad.AnnularReconstruction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients Grad.PhaseAlgebra
open Grad.BoundaryKernelAction Grad.ActualCurrentPrimitives
open Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Allocation

/-- Reuse the accepted original B7 reconstruction-state carrier. The final
annular low ball intersects this existing ball; no duplicate physical state
or assumed coefficient estimates are introduced. -/
abbrev RadialCoefficientState := BoundaryReconstructionState

namespace RadialCoefficientState
variable {parameters : PhaseParameters} {L compact : ℝ}
abbrev data (state : RadialCoefficientState parameters L compact) := state.val
abbrev low (state : RadialCoefficientState parameters L compact) := state.coefficientSmall
end RadialCoefficientState

/-- Reuse the accepted literal row kernel construction at exactly the radial
coefficient envelope. No Fourier mode is discarded. -/
def radialRowKernel (parameters : PhaseParameters) (r : RadialPoint)
    (dimension : ℕ) (coefficient : Fin dimension → ℤ × ℤ → ℂ)
    (moments : ∀ component order,
      Summable (productMoment parameters order r.val (coefficient component))) :
    RadialKernel parameters r dimension 1 :=
  boundaryRowMultiplicationKernel (radialKernelParameters parameters r) dimension
    coefficient (fun component order => by
      simpa only [radialKernelProductMoment] using moments component order)

theorem radialRowKernel_entry (parameters : PhaseParameters) (r : RadialPoint)
    (dimension : ℕ) (coefficient : Fin dimension → ℤ × ℤ → ℂ)
    (moments : ∀ component order,
      Summable (productMoment parameters order r.val (coefficient component)))
    (shift input : ℤ × ℤ) :
    (radialRowKernel parameters r dimension coefficient moments).entry shift input =
      rowMultiplicationEntry dimension coefficient shift input := rfl

theorem radialRowKernel_moment_le (parameters : PhaseParameters) (r : RadialPoint)
    (dimension moment : ℕ) (coefficient : Fin dimension → ℤ × ℤ → ℂ)
    (moments : ∀ component order,
      Summable (productMoment parameters order r.val (coefficient component))) :
    fullKernelMoment (radialKernelParameters parameters r) moment
        (radialRowKernel parameters r dimension coefficient moments) ≤
      Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
        ∑ component, ∑' shift,
          productMoment parameters moment r.val (coefficient component) shift := by
  have bound := boundaryRowMultiplicationKernel_moment_le
    (radialKernelParameters parameters r) dimension moment coefficient
    (fun component order => by
      simpa only [radialKernelProductMoment] using moments component order)
  simp only [radialKernelProductMoment] at bound
  apply bound.trans
  exact mul_le_mul_of_nonneg_right (radialKernelPhaseConstant_le parameters r)
    (Finset.sum_nonneg fun component _ =>
      tsum_nonneg (productMoment_nonnegative parameters moment r.val _))

/-- The same scalar constructor, needed for literal kappa components. -/
def radialScalarKernel (parameters : PhaseParameters) (r : RadialPoint)
    (dimension : ℕ) (coefficient : ℤ × ℤ → ℂ)
    (moments : ∀ order, Summable (productMoment parameters order r.val coefficient)) :
    RadialKernel parameters r dimension dimension :=
  boundaryScalarMultiplicationKernel (radialKernelParameters parameters r) dimension
    coefficient (fun order => by
      simpa only [radialKernelProductMoment] using moments order)

/-- Full rectangular matrix constructor, used by the actual two gauges. -/
def radialMatrixKernel (parameters : PhaseParameters) (r : RadialPoint)
    (input output : ℕ) (coefficient : Fin output → Fin input → ℤ × ℤ → ℂ)
    (moments : ∀ row column order,
      Summable (productMoment parameters order r.val (coefficient row column))) :
    RadialKernel parameters r input output :=
  boundaryMatrixMultiplicationKernel (radialKernelParameters parameters r) input output
    coefficient (fun row column order => by
      simpa only [radialKernelProductMoment] using moments row column order)

theorem radialMatrixKernel_moment_le (parameters : PhaseParameters) (r : RadialPoint)
    (input output moment : ℕ) (coefficient : Fin output → Fin input → ℤ × ℤ → ℂ)
    (moments : ∀ row column order,
      Summable (productMoment parameters order r.val (coefficient row column))) :
    fullKernelMoment (radialKernelParameters parameters r) moment
        (radialMatrixKernel parameters r input output coefficient moments) ≤
      Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
        ∑ row, ∑ column, ∑' shift,
          productMoment parameters moment r.val (coefficient row column) shift := by
  have bound := boundaryMatrixMultiplicationKernel_moment_le
    (radialKernelParameters parameters r) input output moment coefficient
    (fun row column order => by
      simpa only [radialKernelProductMoment] using moments row column order)
  simp only [radialKernelProductMoment] at bound
  apply bound.trans
  exact mul_le_mul_of_nonneg_right (radialKernelPhaseConstant_le parameters r)
    (Finset.sum_nonneg fun row _ => Finset.sum_nonneg fun column _ =>
      tsum_nonneg (productMoment_nonnegative parameters moment r.val _))

end Grad.AnnularReconstruction
