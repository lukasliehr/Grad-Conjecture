import AKCZ10OriginalBranchForwardRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3500
open Set
namespace Grad.NashMoser.InverseCalculus
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.NashMoser.OriginalLimit

theorem branchGrade_large (grade : ℕ) : 3 ≤ grade+4 := by omega

theorem originalSource_norm_mono (parameters : PhaseParameters) (low high : ℕ) (large : 3 ≤ low)
    (ordered : low ≤ high) (source : sourceSmoothRange parameters) :
    ‖sourceSmoothEmbedding parameters low large source‖ ≤
      ‖sourceSmoothEmbedding parameters high (large.trans ordered) source‖ := by
  have bound := sourceLowering_norm_le parameters large ordered
    (sourceSmoothEmbedding parameters high (large.trans ordered) source)
  simpa only [sourceLowering_core] using bound

variable (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain)
    (branch : OriginalFiniteParameter → stateSmoothRange parameters reference insideR)
    (domain : Set OriginalFiniteParameter) (loss : ℕ)
    (inverse : OriginalFiniteParameter → sourceSmoothRange parameters →ₗ[ℝ] stateSmoothRange parameters reference insideR)
    (constant : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constant grade)
    (tame : ∀ grade point, point ∈ domain → ∀ source,
      ‖stateSmoothEmbedding parameters reference insideR (grade+4) (branchGrade_large grade) (inverse point source)‖ ≤
        constant grade*(‖sourceSmoothEmbedding parameters (grade+loss+4) (branchGrade_large (grade+loss)) source‖ +
          (1+‖stateSmoothEmbedding parameters reference insideR (grade+loss+4) (branchGrade_large (grade+loss)) (branch point)‖)*
            ‖sourceSmoothEmbedding parameters (loss+4) (branchGrade_large loss) source‖))

include nonnegative tame in
/-- At a fixed base, the one-high PC bound is a bounded map at every
sufficiently high input grade. The independent low source is only lowered. -/
theorem originalTameInverse_singleGrade (output input : ℕ) (ordered : output+loss ≤ input)
    (point : OriginalFiniteParameter) (member : point ∈ domain) (source : sourceSmoothRange parameters) :
    ‖stateSmoothEmbedding parameters reference insideR (output+4) (branchGrade_large output) (inverse point source)‖ ≤
      (constant output*(2+‖stateSmoothEmbedding parameters reference insideR (output+loss+4)
        (branchGrade_large (output+loss)) (branch point)‖)) *
          ‖sourceSmoothEmbedding parameters (input+4) (branchGrade_large input) source‖ := by
  have high := originalSource_norm_mono parameters (output+loss+4) (input+4)
    (branchGrade_large (output+loss)) (by omega) source
  have low := originalSource_norm_mono parameters (loss+4) (input+4) (branchGrade_large loss) (by omega) source
  apply (tame output point member source).trans
  calc
    _ ≤ constant output*(‖sourceSmoothEmbedding parameters (input+4) (branchGrade_large input) source‖+
        (1+‖stateSmoothEmbedding parameters reference insideR (output+loss+4) (branchGrade_large (output+loss)) (branch point)‖)*
        ‖sourceSmoothEmbedding parameters (input+4) (branchGrade_large input) source‖) :=
      mul_le_mul_of_nonneg_left (add_le_add high (mul_le_mul_of_nonneg_left low (by positivity))) (nonnegative output)
    _ = _ := by ring

/-- The actual core inverse completed at the indicated original grades.
Outside the application domain or below its loss, the harmless totalization
is zero; every theorem uses the actual admissible branch. -/
def originalCompletedBranchInverse (output input : ℕ) (point : OriginalFiniteParameter) :
    sourceRange parameters (input+4) (branchGrade_large input) →L[ℝ]
      stateRange parameters reference insideR (output+4) (branchGrade_large output) := by
  classical
  exact if valid : point ∈ domain ∧ output+loss ≤ input then
    completedOriginalInverse parameters reference insideR (input+4) (output+4)
      (branchGrade_large input) (branchGrade_large output) (inverse point)
      (constant output*(2+‖stateSmoothEmbedding parameters reference insideR (output+loss+4)
        (branchGrade_large (output+loss)) (branch point)‖))
      (originalTameInverse_singleGrade parameters reference insideR branch domain loss inverse constant nonnegative tame
        output input valid.2 point valid.1)
  else 0

theorem originalCompletedBranchInverse_core (output input : ℕ) (ordered : output+loss ≤ input)
    (point : OriginalFiniteParameter) (member : point ∈ domain) (source : sourceSmoothRange parameters) :
    originalCompletedBranchInverse parameters reference insideR branch domain loss inverse constant nonnegative tame output input point
      (sourceSmoothEmbedding parameters (input+4) (branchGrade_large input) source) =
        stateSmoothEmbedding parameters reference insideR (output+4) (branchGrade_large output) (inverse point source) := by
  rw [originalCompletedBranchInverse,dif_pos ⟨member,ordered⟩,completedOriginalInverse_core]

theorem originalCompletedBranchInverse_norm_bound (output input : ℕ) (ordered : output+loss ≤ input)
    (point : OriginalFiniteParameter) (member : point ∈ domain) :
    ‖originalCompletedBranchInverse parameters reference insideR branch domain loss inverse constant nonnegative tame output input point‖ ≤
      constant output*(2+‖stateSmoothEmbedding parameters reference insideR (output+loss+4)
        (branchGrade_large (output+loss)) (branch point)‖) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (nonnegative output) (by positivity))
  intro source
  rw [originalCompletedBranchInverse,dif_pos ⟨member,ordered⟩]
  exact completedOriginalInverse_bound parameters reference insideR (input+4) (output+4)
    (branchGrade_large input) (branchGrade_large output) (inverse point) _ _ source

end Grad.NashMoser.InverseCalculus
