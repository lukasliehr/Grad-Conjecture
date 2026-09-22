import AKCW6ActualJointPartialDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter
open scoped ContDiff Topology
namespace Grad.OriginalParameterEvaluation
open Grad.CartesianState Grad.ClosedJets Grad.DiskExtension.Operator

variable {dimension : ℕ} (parameters : PhaseParameters)
variable {Parameter : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]

def originalJointDerivative (order : ℕ) (field : Parameter → ACore parameters dimension)
    (point : Parameter × SpatialCell) :
    (Parameter × SpatialCell) →L[ℝ] SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension :=
  (originalClampedParameterDerivative parameters order field point.1 point.2).coprod
    (originalClampedDerivative parameters (order+1) (field point.1) point.2).curryLeft

theorem originalClampedSpatialDerivative_continuous
    {domain : Set Parameter} (order : ℕ) (field : Parameter → ACore parameters dimension)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (completedCoreBranch parameters field grade) domain) :
    ContinuousOn (fun point : Parameter × SpatialCell =>
      (originalClampedDerivative parameters (order+1) (field point.1) point.2).curryLeft) (domain ×ˢ univ) :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (order+1) => SpatialCell)
    (ComplexEuclidean dimension)).continuous.comp_continuousOn
      (originalClampedDerivative_joint_continuous parameters (order+1) field (smooth (order+1+3)))

/-- The actual parameter and actual spatial partials assemble into the
joint Fréchet derivative on the SAME open parameter set and fixed collar. -/
theorem originalJointDerivative_hasFDerivAt [FiniteDimensional ℝ Parameter]
    {domain : Set Parameter} (openDomain : IsOpen domain) (order : ℕ)
    (field : Parameter → ACore parameters dimension)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (completedCoreBranch parameters field grade) domain)
    (point : Parameter × SpatialCell) (member : point∈domain ×ˢ originalOpenCollar) :
    HasFDerivAt (fun input : Parameter × SpatialCell =>
      originalClampedDerivative parameters order (field input.1) input.2)
      (originalJointDerivative parameters order field point) point := by
  apply HasStrictFDerivAt.hasFDerivAt
  apply hasStrictFDerivAt_uncurry_coprod
    (f := fun parameter spatial => originalClampedDerivative parameters order (field parameter) spatial)
    (f₁ := originalClampedParameterDerivative parameters order field)
    (f₂ := fun parameter spatial => (originalClampedDerivative parameters (order+1) (field parameter) spatial).curryLeft)
  · filter_upwards [(openDomain.prod isOpen_univ).mem_nhds ⟨member.1, mem_univ _⟩] with nearby inside
    exact originalClampedParameterDerivative_hasFDerivAt parameters order field nearby.1 nearby.2
      (completedCoreBranch_differentiableAt parameters openDomain field smooth nearby.1 inside.1 (order+3))
  · filter_upwards [(isOpen_univ.prod originalOpenCollar_isOpen).mem_nhds ⟨mem_univ _, member.2⟩] with nearby inside
    exact originalClampedDerivative_spatial parameters order (field nearby.1) nearby.2 inside.2
  · exact (originalClampedParameterDerivative_continuous parameters openDomain order field smooth).continuousAt
      ((openDomain.prod isOpen_univ).mem_nhds ⟨member.1,mem_univ _⟩)
  · exact (originalClampedSpatialDerivative_continuous parameters order field smooth).continuousAt
      ((openDomain.prod isOpen_univ).mem_nhds ⟨member.1,mem_univ _⟩)

end Grad.OriginalParameterEvaluation
