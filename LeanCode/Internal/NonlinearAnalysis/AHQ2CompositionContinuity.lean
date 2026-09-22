import AHQ1UniformKernelEntryDecay

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.AnnularKernelContinuity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryKernelAction

variable {X : Type*} [TopologicalSpace X] {src mid tgt : ℕ}
    (parameters : X → PhaseParameters)

/-- Parameter-dependent full input-mode kernels compose continuously. The
summable majorant comes from the actual inner fourth moment, uniformly over
the parameter; the outer kernel only needs its actual zero moment. -/
theorem fullKernelComposition_continuous
    (outer : (x : X) → FullTwoFrequencyKernel (parameters x) mid tgt)
    (inner : (x : X) → FullTwoFrequencyKernel (parameters x) src mid)
    (outerContinuous : ∀ shift input, Continuous (fun x => (outer x).entry shift input))
    (innerContinuous : ∀ shift input, Continuous (fun x => (inner x).entry shift input))
    (outerBound innerBound : ℝ) (outerNonnegative : 0 ≤ outerBound)
    (outerUniform : ∀ x, fullKernelMoment (parameters x) 0 (outer x) ≤ outerBound)
    (innerUniform : ∀ x, fullKernelMoment (parameters x) 4 (inner x) ≤ innerBound)
    (total input : ℤ × ℤ) :
    Continuous (fun x => (fullKernelComposition (outer x) (inner x)).entry total input) := by
  change Continuous (fun x => ∑' middle : ℤ × ℤ,
    ((outer x).entry (total - middle) (input + middle)).comp ((inner x).entry middle input))
  apply continuous_tsum
    (fun middle => (outerContinuous (total - middle) (input + middle)).clm_comp (innerContinuous middle input))
    ((fullLattice_decay_summable.mul_left innerBound).mul_left outerBound)
  intro middle x
  apply (fullKernelCompositionTerm_norm_le (outer x) (inner x) total middle input).trans
  exact mul_le_mul
    ((fullKernelMoment_entryNorm_le (parameters x) (outer x) (total - middle)).trans (outerUniform x))
    (fullKernelEntryNorm_decay (parameters x) (inner x) 4 innerBound (innerUniform x) middle)
    (fullKernelEntryNorm_nonnegative (inner x) middle) outerNonnegative

end Grad.AnnularKernelContinuity
