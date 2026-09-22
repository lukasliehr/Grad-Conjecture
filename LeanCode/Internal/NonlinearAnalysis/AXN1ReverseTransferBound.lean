import AXB4LiftBoundConsumer
import QY23TransferCoreBounds

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

open scoped ContDiff

namespace Grad.ChartAxisSourceBound

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.NonlinearQuotientBounds Grad.Constraints.Gauges
open Grad.NonlinearProduct Grad.MixedQuotientComposition

/-- The reverse N18 operator family, with the first seed varying and the
second seed fixed, is genuinely smooth in the completed same-grade operator
norm.  This is the orientation used by the fixed-reference cap lift. -/
theorem completedReverseSeedTransferFamily_contDiffOn
    (parameters : PhaseParameters) (grade : ℕ) (reference : Seed.Parameters) :
    ContDiffOn ℝ ∞
      (fun seed => completedSeedTransferFamily parameters grade seed reference)
      Seed.parameterDomain := by
  let planarPart := q23ValueMapCompleted (grade := grade) parameters planarPartMap
  let planarInclusion := q23ValueMapCompleted (grade := grade) parameters planarInclusionMap
  let toroidalPart := q23ValueMapCompleted (grade := grade) parameters toroidalPartMap
  let toroidalInclusion := q23ValueMapCompleted (grade := grade) parameters toroidalInclusionMap
  let angular := angularCompleted (dimension := 1) (grade := grade) parameters 0
  have inverse : ContDiffOn ℝ ∞
      (fun seed => completedSeedInverseFixed parameters grade seed)
      Seed.parameterDomain :=
    contDiffOn_const.add (completedSeedDeviationFamily_contDiffOn parameters grade 1)
  have sliceInverse := q23ContDiffOn_complexCLM_comp
    (contDiffOn_const : ContDiffOn ℝ ∞
      (fun _ : Seed.Parameters => completedSeedSliceFamily parameters grade reference)
        Seed.parameterDomain) inverse
  have planar := q23ContDiffOn_complexCLM_comp
    (contDiffOn_const : ContDiffOn ℝ ∞
      (fun _ : Seed.Parameters => completedSeedMatrixFamily parameters grade reference)
        Seed.parameterDomain) sliceInverse
  have planarInput := q23ContDiffOn_complexCLM_comp planar
    (contDiffOn_const : ContDiffOn ℝ ∞
      (fun _ : Seed.Parameters => planarPart) Seed.parameterDomain)
  have planarOutput := q23ContDiffOn_complexCLM_comp
    (contDiffOn_const : ContDiffOn ℝ ∞
      (fun _ : Seed.Parameters => planarInclusion) Seed.parameterDomain) planarInput
  have dotPlanar := q23ContDiffOn_complexCLM_comp
    (contDiffOn_const : ContDiffOn ℝ ∞
      (fun _ : Seed.Parameters => completedSeedDerivativeDotFamily parameters grade reference)
        Seed.parameterDomain) planarInput
  have meanDot := q23ContDiffOn_complexCLM_comp
    (contDiffOn_const : ContDiffOn ℝ ∞
      (fun _ : Seed.Parameters => angular) Seed.parameterDomain) dotPlanar
  have toroidalFixed : ContDiffOn ℝ ∞
      (fun _ : Seed.Parameters => toroidalPart - angular.comp toroidalPart)
      Seed.parameterDomain := contDiffOn_const
  have toroidalScalar := toroidalFixed.sub
    (meanDot.const_smul (parameters.length⁻¹ : ℂ))
  have toroidalOutput := q23ContDiffOn_complexCLM_comp
    (contDiffOn_const : ContDiffOn ℝ ∞
      (fun _ : Seed.Parameters => toroidalInclusion) Seed.parameterDomain) toroidalScalar
  change ContDiffOn ℝ ∞ (fun seed =>
    planarInclusion.comp
        ((completedPlanarTransferFamily parameters grade seed reference).comp planarPart) +
      toroidalInclusion.comp
        ((toroidalPart - angular.comp toroidalPart) -
          (parameters.length⁻¹ : ℂ) • angular.comp
            ((completedSeedDerivativeDotFamily parameters grade reference).comp
              ((completedPlanarTransferFamily parameters grade seed reference).comp
                planarPart)))) Seed.parameterDomain
  exact planarOutput.add toroidalOutput

/-- Same-grade N18 bounds in the reverse orientation are uniform on every
compact admissible seed patch.  No equivalent norm or grade shift is used. -/
theorem reverseSeedTransferCore_bound_on_patch
    (parameters : PhaseParameters) (grade : ℕ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ seed ∈ seedPatch, ∀ (inside : seed ∈ Seed.parameterDomain)
        (field : ACore parameters 3),
        originalGradeNorm grade
            (seedTransfer parameters seed inside reference insideR field) ≤
          constant * originalGradeNorm grade field := by
  have realSmooth : ContDiffOn ℝ ∞
      (fun seed => (completedSeedTransferFamily parameters grade seed reference).restrictScalars ℝ)
      Seed.parameterDomain :=
    (q23RestrictScalarsCLM
      (E := AGrade parameters 3 grade) (F := AGrade parameters 3 grade)).contDiff.comp_contDiffOn
        (completedReverseSeedTransferFamily_contDiffOn parameters grade reference)
  have bounded : ∃ constant : ℝ, ∀ seed ∈ seedPatch,
      ‖(completedSeedTransferFamily parameters grade seed reference).restrictScalars ℝ‖ ≤
        constant := by
    exact compact.exists_bound_of_continuousOn
      (f := fun seed =>
        (completedSeedTransferFamily parameters grade seed reference).restrictScalars ℝ)
      (realSmooth.continuousOn.mono insidePatch)
  obtain ⟨constant, bound⟩ := bounded
  refine ⟨max 0 constant, le_max_left _ _, ?_⟩
  intro seed member inside field
  have operatorBound : ‖completedSeedTransferFamily parameters grade seed reference‖ ≤
      max 0 constant := by
    simpa only [ContinuousLinearMap.norm_restrictScalars] using
      (bound seed member).trans (le_max_right 0 constant)
  have evaluation :=
    (completedSeedTransferFamily parameters grade seed reference).le_opNorm
      (q23ACoreEta parameters 3 grade field)
  change ‖completedSeedTransferFamily parameters grade seed reference
      (aGradeEta parameters (GradeCore.ofCoreLinear field))‖ ≤
    ‖completedSeedTransferFamily parameters grade seed reference‖ *
      ‖aGradeEta parameters (GradeCore.ofCoreLinear field)‖ at evaluation
  rw [completedSeedTransferFamily_core parameters grade seed inside reference insideR field,
    aGradeEta_norm, aGradeEta_norm] at evaluation
  change originalGradeNorm grade
      (seedTransfer parameters seed inside reference insideR field) ≤
    ‖completedSeedTransferFamily parameters grade seed reference‖ *
      originalGradeNorm grade field at evaluation
  exact evaluation.trans
    (mul_le_mul_of_nonneg_right operatorBound
      (originalGradeNorm_nonnegative grade field))

end Grad.ChartAxisSourceBound
