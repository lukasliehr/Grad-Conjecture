import BCI25OriginalBoundaryInverseConsumer

noncomputable section

namespace Grad.AnnularReconstruction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients Grad.PhaseAlgebra
open Grad.BoundaryKernelAction

/-- A radius in the original closed disk. Positive annular lower bounds are
imposed only where the physical factors `1/r` are used. -/
abbrev RadialPoint := Set.Icc (0 : ℝ) 1

/-- Reindex the accepted full-kernel algebra so its boundary envelope equals
exactly the original coefficient envelope at `r`. This does not alter the
physical state, source spaces, or their original phase. -/
def radialKernelParameters (parameters : PhaseParameters) (r : RadialPoint) :
    PhaseParameters where
  length := parameters.length
  sigma0 := parameters.sigma0 + parameters.gamma * (1 - r.val)
  gamma := parameters.gamma
  length_pos := parameters.length_pos
  sigma0_pos := lt_of_lt_of_le parameters.sigma0_pos (by
    have := mul_nonneg parameters.gamma_pos.le (sub_nonneg.mpr r.property.2)
    linarith)
  gamma_pos := parameters.gamma_pos
  gamma_lt_min := by
    apply lt_min (lt_min_iff.mp parameters.gamma_lt_min).1
    have := (lt_min_iff.mp parameters.gamma_lt_min).2
    have := mul_nonneg parameters.gamma_pos.le (sub_nonneg.mpr r.property.2)
    linarith

@[simp] theorem radialKernelParameters_one (parameters : PhaseParameters) :
    radialKernelParameters parameters ⟨1, zero_le_one, le_rfl⟩ = parameters := by
  cases parameters
  simp [radialKernelParameters]

abbrev RadialKernel (parameters : PhaseParameters) (r : RadialPoint)
    (input output : ℕ) :=
  FullTwoFrequencyKernel (radialKernelParameters parameters r) input output

/-- Literal equality of the two coefficient envelopes, at every full cell. -/
theorem radialKernelEnvelope (parameters : PhaseParameters) (r : RadialPoint)
    (cell : ℤ) :
    coefficientRadialEnvelope (radialKernelParameters parameters r) cell 1 =
      coefficientRadialEnvelope parameters cell r.val := by
  unfold coefficientRadialEnvelope radialKernelParameters
  congr 2
  ring

@[simp] theorem radialKernelProductMoment (parameters : PhaseParameters)
    (r : RadialPoint) (moment : ℕ) (coefficient : ℤ × ℤ → ℂ) :
    productMoment (radialKernelParameters parameters r) moment 1 coefficient =
      productMoment parameters moment r.val coefficient := by
  funext mode
  unfold productMoment
  rw [radialKernelEnvelope]

/-- The full-kernel norm retains the exact original radial analytic width. -/
theorem radialKernelPhaseCost (parameters : PhaseParameters) (r : RadialPoint)
    (shift : ℤ × ℤ) :
    boundaryCoefficientPhaseCost (radialKernelParameters parameters r) shift =
      Real.exp (parameters.sigma0 + parameters.gamma * (2 - r.val)) *
        coefficientRadialEnvelope parameters shift.2 r.val := by
  unfold boundaryCoefficientPhaseCost phaseWeight phaseWidth
    coefficientRadialEnvelope radialKernelParameters
  congr 1 <;> congr 1 <;> ring

/-- One prefactor works on the entire original radial interval. -/
theorem radialKernelPhaseConstant_le (parameters : PhaseParameters) (r : RadialPoint) :
    Real.exp ((radialKernelParameters parameters r).sigma0 +
      (radialKernelParameters parameters r).gamma) ≤
      Real.exp (parameters.sigma0 + 2 * parameters.gamma) := by
  apply Real.exp_le_exp.mpr
  dsimp [radialKernelParameters]
  have := mul_nonneg parameters.gamma_pos.le r.property.1
  nlinarith

end Grad.AnnularReconstruction
