import AKCW8SameOriginalJointSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
open Set
open scoped ContDiff
namespace Grad.OriginalParameterEvaluation
open Grad.CartesianState Grad.ClosedJets Grad.Constraints Grad.PhysicalCoordinates
open Grad.Q24Realization Grad.NonlinearQuotientBounds

variable (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference∈Seed.parameterDomain)
variable {Parameter : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]

/-- The actual original physical chart on every admissible parameter.
The totalization is irrelevant on the stated open parameter set. -/
def originalPhysicalChartBranch (input : Parameter → Seed.Parameters × JointState parameters)
    (point : Parameter) : QuotientState parameters := by
  classical
  exact if insideS : (input point).1∈Seed.parameterDomain then
    physicalReferenceState parameters reference insideR (input point).1 insideS (input point).2
    else 0

omit [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter] in
theorem originalPhysicalChartBranch_same (input : Parameter → Seed.Parameters × JointState parameters)
    (point : Parameter) (insideS : (input point).1∈Seed.parameterDomain) :
    originalPhysicalChartBranch parameters reference insideR input point=
      physicalReferenceState parameters reference insideR (input point).1 insideS (input point).2 := by
  unfold originalPhysicalChartBranch
  rw [dif_pos insideS]

theorem originalPhysicalChartBranch_completed_smooth {domain : Set Parameter}
    (input : Parameter → Seed.Parameters × JointState parameters)
    (admissible : ∀ point∈domain, (input point).1∈Seed.parameterDomain ∧ ChartAxisCondition (input point).2.2)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (fun point => mixedCoreEmbed parameters grade (input point)) domain)
    (grade : ℕ) :
    ContDiffOn ℝ ∞ (fun point => polynomialStateEmbed parameters grade
      (originalPhysicalChartBranch parameters reference insideR input point)) domain := by
  have composed := (completedPhysicalMixedReferenceState_contDiffOn parameters reference grade).comp
    (smooth grade) (fun point member => (mixedDomain_core_iff parameters grade (input point)).mpr (admissible point member))
  apply composed.congr
  intro point member
  rw [originalPhysicalChartBranch_same parameters reference insideR input point (admissible point member).1]
  exact (completedPhysicalMixedReferenceState_core parameters reference insideR grade (input point)
    (admissible point member).1 (admissible point member).2).symm

theorem originalPhysicalChartBranch_fields_smooth {domain : Set Parameter}
    (input : Parameter → Seed.Parameters × JointState parameters)
    (admissible : ∀ point∈domain, (input point).1∈Seed.parameterDomain ∧ ChartAxisCondition (input point).2.2)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (fun point => mixedCoreEmbed parameters grade (input point)) domain)
    (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedCoreBranch parameters
      (fun point => (originalPhysicalChartBranch parameters reference insideR input point).2.1) grade) domain ∧
    ContDiffOn ℝ ∞ (completedCoreBranch parameters
      (fun point => (originalPhysicalChartBranch parameters reference insideR input point).2.2) grade) domain := by
  have outer := (WithLp.prodContinuousLinearEquiv 1 ℝ ℂ
    (WithLp 1 (AGrade parameters 3 grade × AGrade parameters 1 grade))).contDiff.comp_contDiffOn
      (originalPhysicalChartBranch_completed_smooth parameters reference insideR input admissible smooth grade)
  have fields := (WithLp.prodContinuousLinearEquiv 1 ℝ
    (AGrade parameters 3 grade) (AGrade parameters 1 grade)).contDiff.comp_contDiffOn outer.snd
  exact ⟨fields.fst,fields.snd⟩

/-- Actual original physical vector and potential, jointly C∞ on one fixed
radius-4/3 collar. Every completed smoothness input belongs to the SAME
original mixed chart family; no PDE or inverse estimate is assumed here. -/
theorem originalPhysicalChartBranch_joint_smooth [FiniteDimensional ℝ Parameter]
    {domain : Set Parameter} (openDomain : IsOpen domain)
    (input : Parameter → Seed.Parameters × JointState parameters)
    (admissible : ∀ point∈domain, (input point).1∈Seed.parameterDomain ∧ ChartAxisCondition (input point).2.2)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (fun point => mixedCoreEmbed parameters grade (input point)) domain) :
    ContDiffOn ℝ ∞ (fun point : Parameter × SpatialCell =>
      originalExtendedField parameters (originalPhysicalChartBranch parameters reference insideR input point.1).2.1 point.2)
      (domain ×ˢ originalOpenCollar) ∧
    ContDiffOn ℝ ∞ (fun point : Parameter × SpatialCell =>
      originalExtendedField parameters (originalPhysicalChartBranch parameters reference insideR input point.1).2.2 point.2)
      (domain ×ˢ originalOpenCollar) := by
  have vectorSmooth : ∀ grade, ContDiffOn ℝ ∞ (completedCoreBranch parameters
      (fun point => (originalPhysicalChartBranch parameters reference insideR input point).2.1) grade) domain :=
    fun grade => (originalPhysicalChartBranch_fields_smooth parameters reference insideR input admissible smooth grade).1
  have scalarSmooth : ∀ grade, ContDiffOn ℝ ∞ (completedCoreBranch parameters
      (fun point => (originalPhysicalChartBranch parameters reference insideR input point).2.2) grade) domain :=
    fun grade => (originalPhysicalChartBranch_fields_smooth parameters reference insideR input admissible smooth grade).2
  exact ⟨originalExtendedField_joint_contDiffOn (dimension := 3) parameters openDomain
      (fun point => (originalPhysicalChartBranch parameters reference insideR input point).2.1) vectorSmooth,
    originalExtendedField_joint_contDiffOn (dimension := 1) parameters openDomain
      (fun point => (originalPhysicalChartBranch parameters reference insideR input point).2.2) scalarSmooth⟩

end Grad.OriginalParameterEvaluation
