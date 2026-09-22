import AKCZ16OriginalZeroBranchSmoothness
import AKCW9ActualChartFamilyEvaluation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 3500
open Set
open scoped ContDiff
namespace Grad.NashMoser.InverseCalculus
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.Q24Realization Grad.PhysicalCoordinates Grad.NonlinearQuotientBounds Grad.SmoothForward
open Grad.NashMoser.OriginalLimit Grad.OriginalParameterEvaluation Grad.ClosedJets

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

variable (cellLength : ℝ)
    (admissible : ∀ point ∈ domain, point.1 ∈ Seed.parameterDomain ∧
      ChartAxisCondition (smoothingChartCore parameters (branch point).val))
    (right : ∀ point (member : point ∈ domain), ∀ source,
      literalPhysicalSmoothForward parameters cellLength reference insideR point.1 (admissible point member).1
        (point.2,branch point) (admissible point member).2 (inverse point source) = source)
    (left : ∀ point (member : point ∈ domain), ∀ state,
      inverse point (literalPhysicalSmoothForward parameters cellLength reference insideR point.1 (admissible point member).1
        (point.2,branch point) (admissible point member).2 state) = state)

include right left nonnegative tame in
/-- Every original complex mixed grade, including grades below four, is
obtained by its actual inclusion from the proven real constrained branch. -/
theorem originalZeroBranch_mixedCore_smooth (openDomain : IsOpen domain)
    (continuous : ∀ grade, ContinuousOn (fun point => stateSmoothEmbedding parameters reference insideR
      (grade+4) (branchGrade_large grade) (branch point)) domain)
    (zeros : ∀ point ∈ domain, originalNonlinearSource parameters cellLength reference insideR point (branch point)=0)
    (grade : ℕ) :
    ContDiffOn ℝ ∞ (fun point => mixedCoreEmbed parameters grade
      (point.1,realJointCoreToJoint parameters reference insideR (point.2,branch point))) domain := by
  let : NormedSpace ℝ (RealJointAmbient parameters reference insideR (grade+4) (branchGrade_large grade)) := inferInstance
  let : NormedSpace ℝ (RealMixedAmbient parameters reference insideR (grade+4) (branchGrade_large grade)) := inferInstance
  have smooth := originalZeroBranch_contDiffOn parameters reference insideR branch domain loss inverse constant nonnegative tame
    cellLength admissible right left openDomain continuous zeros grade
  have mixed := originalMixedBranch_contDiffOn parameters reference insideR branch (grade+4) (branchGrade_large grade) ∞ domain smooth
  have included := (realMixedInclusion parameters reference insideR (grade+4) (branchGrade_large grade)).contDiff.comp_contDiffOn mixed
  have lowered := (mixedLowering parameters (show grade ≤ grade+4 by omega)).contDiff.comp_contDiffOn included
  apply lowered.congr
  intro point member
  simp only [Function.comp_apply]
  rw [realMixedInclusion_core,mixedLowering_core]

include right left nonnegative tame in
/-- Exact physical consumer: the vector and scalar potential of the SAME
original zero branch are jointly smooth on one fixed radius-4/3 collar.
The remaining analytic input is the actual two-sided tame inverse. -/
theorem originalZeroBranch_physical_joint_smooth (openDomain : IsOpen domain)
    (continuous : ∀ grade, ContinuousOn (fun point => stateSmoothEmbedding parameters reference insideR
      (grade+4) (branchGrade_large grade) (branch point)) domain)
    (zeros : ∀ point ∈ domain, originalNonlinearSource parameters cellLength reference insideR point (branch point)=0) :
    ContDiffOn ℝ ∞ (fun point : OriginalFiniteParameter × SpatialCell =>
      originalExtendedField parameters (originalPhysicalChartBranch parameters reference insideR
        (fun parameter => (parameter.1,realJointCoreToJoint parameters reference insideR (parameter.2,branch parameter))) point.1).2.1 point.2)
      (domain ×ˢ originalOpenCollar) ∧
    ContDiffOn ℝ ∞ (fun point : OriginalFiniteParameter × SpatialCell =>
      originalExtendedField parameters (originalPhysicalChartBranch parameters reference insideR
        (fun parameter => (parameter.1,realJointCoreToJoint parameters reference insideR (parameter.2,branch parameter))) point.1).2.2 point.2)
      (domain ×ˢ originalOpenCollar) := by
  apply originalPhysicalChartBranch_joint_smooth parameters reference insideR openDomain
    (fun point => (point.1,realJointCoreToJoint parameters reference insideR (point.2,branch point)))
  · exact admissible
  · exact originalZeroBranch_mixedCore_smooth parameters reference insideR branch domain loss inverse constant nonnegative tame
      cellLength admissible right left openDomain continuous zeros

end Grad.NashMoser.InverseCalculus
