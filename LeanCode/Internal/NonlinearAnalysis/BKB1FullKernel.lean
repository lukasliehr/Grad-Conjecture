import BKA12ExactHalfRatio

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace

/-- A genuine AE7 two-frequency kernel.  `entry shift input` is the
matrix entry from `input` to `input + shift`; in particular the entry is
allowed to depend on the input mode.  `entryNorm` is required to be the
literal supremum of the entry norms, not merely a chosen majorant. -/
structure FullTwoFrequencyKernel (parameters : PhaseParameters)
    (sourceDimension targetDimension : ℕ) where
  entry : (ℤ × ℤ) → (ℤ × ℤ) →
    (ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
  entryNorm : (ℤ × ℤ) → ℝ
  entry_le : ∀ shift input, ‖entry shift input‖ ≤ entryNorm shift
  entryNorm_le : ∀ shift bound, (∀ input, ‖entry shift input‖ ≤ bound) →
    entryNorm shift ≤ bound
  moments : ∀ moment : ℕ, Summable (fun shift : ℤ × ℤ =>
    boundaryCoefficientPhaseCost parameters shift *
      annularFrequency shift.1 shift.2 ^ moment * entryNorm shift)

/-- The manuscript envelope moment at the boundary width.  The phase
parameter is explicit here; the kernel's summability field below is restated
for every admissible phase rather than baking a particular phase into its
entries. -/
def fullKernelMoment {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (moment : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension) : ℝ :=
  ∑' shift : ℤ × ℤ,
    boundaryCoefficientPhaseCost parameters shift *
      annularFrequency shift.1 shift.2 ^ moment * kernel.entryNorm shift

theorem fullKernelEntryNorm_nonnegative {sourceDimension targetDimension : ℕ}
    {parameters : PhaseParameters}
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift : ℤ × ℤ) : 0 ≤ kernel.entryNorm shift := by
  exact (norm_nonneg (kernel.entry shift (0, 0))).trans
    (kernel.entry_le shift (0, 0))

theorem fullKernelMoment_nonnegative {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (moment : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension) :
    0 ≤ fullKernelMoment parameters moment kernel := by
  unfold fullKernelMoment
  exact tsum_nonneg fun shift =>
    mul_nonneg
      (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters shift)
        (pow_nonneg (annularFrequency_pos shift).le _))
      (fullKernelEntryNorm_nonnegative kernel shift)

end Grad.BoundaryKernelAction
