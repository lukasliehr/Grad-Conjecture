import AKDC4FixedOpenNewtonDomain

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3500
open Set Filter
open scoped Topology

namespace Grad.NashMoser.OriginalIteration
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.SmoothingFamily Grad.Q24Realization Grad.NashMoser.OriginalLimit Grad.SmoothForward Grad.NashMoser.Numeric
open Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates Grad.NashMoser.InverseCalculus

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}
    {inverse : OriginalNewtonInverse neighborhood cellLength loss}

namespace OriginalNewtonScale
variable (scale : OriginalNewtonScale inverse)

/-- Actual finite-stage continuity is proved by induction from the literal
Newton step, not supplied to the limit theorem as an extra hypothesis. -/
theorem parameterIterate_continuousOn (leftLaw : inverse.LeftLaw) (index : ℕ) :
    ∀ grade, ContinuousOn (fun point => stateSmoothEmbedding parameters reference inside (grade+4)
      (branchGrade_large grade) (scale.parameterIterate index point)) scale.openParameterDomain := by
  induction index with
  | zero =>
    intro grade
    simpa only [scale.parameterIterate_zero] using (continuousOn_const : ContinuousOn
      (fun _ : OriginalFiniteParameter => stateSmoothEmbedding parameters reference inside (grade+4)
        (branchGrade_large grade) (0 : stateSmoothRange parameters reference inside)) scale.openParameterDomain)
  | succ index inductionHypothesis =>
    intro grade
    have step := inverse.originalNewtonStep_continuousOn leftLaw scale.openParameterDomain
      scale.openParameterDomain_isOpen (fun point member => (scale.openParameterDomain_subset member).1)
      (scale.parameterIterate index) (scale.parameterIterate_low index) inductionHypothesis
      (newtonTime scale.initial index) (newtonTime_pos (by linarith [scale.initialLarge]) index) grade
    apply step.congr
    intro point member
    exact congrArg (stateSmoothEmbedding parameters reference inside (grade+4) (branchGrade_large grade))
      (scale.parameterIterate_step index point member)

/-- Uniform convergence of the original finite stages on the SAME open
parameter patch follows from the accepted CY convergence on its parent set. -/
theorem parameterLimit_uniformOn (grade : ℕ) :
    TendstoUniformlyOn (fun index point => stateSmoothEmbedding parameters reference inside (grade+4)
      (branchGrade_large grade) (scale.parameterIterate index point))
      (fun point => stateSmoothEmbedding parameters reference inside (grade+4) (branchGrade_large grade)
        (scale.parameterLimit point)) atTop scale.openParameterDomain := by
  intro entourage entourageMember
  filter_upwards [(scale.originalLimit_uniform ⟨grade+4,branchGrade_large grade⟩) entourage entourageMember] with index bound
  intro point member
  rw [scale.parameterLimit_same point (scale.openParameterDomain_subset member),
    scale.parameterIterate_same index point (scale.openParameterDomain_subset member)]
  exact bound ⟨point,scale.openParameterDomain_subset member⟩

/-- The SAME actual original zero limit is continuous in all completed
grades, now with no finite-iterate continuity premise. -/
theorem parameterLimit_continuousOn (leftLaw : inverse.LeftLaw) (grade : ℕ) :
    ContinuousOn (fun point => stateSmoothEmbedding parameters reference inside (grade+4)
      (branchGrade_large grade) (scale.parameterLimit point)) scale.openParameterDomain :=
  (scale.parameterLimit_uniformOn grade).continuousOn
    (Frequently.of_forall (fun index => scale.parameterIterate_continuousOn leftLaw index grade))

end OriginalNewtonScale
end Grad.NashMoser.OriginalIteration
