import AHQ5RegularKernelAlgebra
import AHP7UniformRadialGaugeBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.AnnularKernelContinuity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularReconstruction

/-- A fixed literal entry family remains continuous and uniformly bounded
when only the bookkeeping phase changes to the actual radius. -/
theorem fixedRadialKernel_regular (parameters : PhaseParameters) {src tgt : ℕ}
    (family : (p : PhaseParameters) → FullTwoFrequencyKernel p src tgt)
    (same : ∀ first second, SameKernelEntries (family first) (family second)) :
    RegularKernelFamily (fun r : RadialPoint => family (radialKernelParameters parameters r)) := by
  refine regularKernelFamily_of_bound _ ?_
    (fun moment => fullKernelMoment (maximalKernelParameters parameters) moment (family (maximalKernelParameters parameters))) ?_
  · intro shift input
    have equal : (fun r : RadialPoint => (family (radialKernelParameters parameters r)).entry shift input) =
        (fun _ : RadialPoint => (family (maximalKernelParameters parameters)).entry shift input) :=
      funext (fun r => same _ _ shift input)
    rw [equal]
    exact continuous_const
  · intro moment r
    exact (same _ _).radialMoment_le parameters r moment

theorem identityRadialKernel_regular (parameters : PhaseParameters) (dimension : ℕ) :
    RegularKernelFamily (fun r : RadialPoint => fullIdentityKernel (radialKernelParameters parameters r) dimension) :=
  fixedRadialKernel_regular parameters _ (fun first second => sameFullIdentityKernel first second dimension)

theorem constantMatrixRadialKernel_regular (parameters : PhaseParameters) (src tgt : ℕ)
    (mapping : ComplexEuclidean src →L[ℂ] ComplexEuclidean tgt) :
    RegularKernelFamily (fun r : RadialPoint => constantMatrixKernel (radialKernelParameters parameters r) src tgt mapping) :=
  fixedRadialKernel_regular parameters _ (fun first second => sameConstantMatrixKernel first second src tgt mapping)

theorem scalarModeRadialKernel_regular (parameters : PhaseParameters) (dimension : ℕ)
    (multiplier : ℤ × ℤ → ℂ) (bound : ℝ) (bounded : ∀ mode, ‖multiplier mode‖ ≤ bound) :
    RegularKernelFamily (fun r : RadialPoint => scalarModeDiagonalKernel (radialKernelParameters parameters r) dimension multiplier bound bounded) :=
  fixedRadialKernel_regular parameters _ (fun first second => sameScalarModeDiagonalKernel first second dimension multiplier bound bounded)

end Grad.AnnularKernelContinuity
