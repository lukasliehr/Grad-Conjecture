import AKCW7OriginalJointFrechetDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
open scoped ContDiff Topology
namespace Grad.OriginalParameterEvaluation
open Grad.CartesianState Grad.ClosedJets Grad.DiskExtension.Operator

variable {dimension : ℕ} (parameters : PhaseParameters)
variable {Parameter : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
variable [FiniteDimensional ℝ Parameter]

/-- The finite-order induction uses the SAME original parameter derivative
and the next actual spatial extension derivative. -/
theorem originalClampedDerivative_joint_contDiffOn_nat
    {domain : Set Parameter} (openDomain : IsOpen domain) (order spatialOrder : ℕ)
    (field : Parameter → ACore parameters dimension)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (completedCoreBranch parameters field grade) domain) :
    ContDiffOn ℝ order (fun point : Parameter × SpatialCell =>
      originalClampedDerivative parameters spatialOrder (field point.1) point.2)
      (domain ×ˢ originalOpenCollar) := by
  induction order generalizing field spatialOrder with
  | zero =>
    apply contDiffOn_zero.mpr
    exact (originalClampedDerivative_joint_continuous parameters spatialOrder field (smooth (spatialOrder+3))).mono
      (fun point member => ⟨member.1,mem_univ point.2⟩)
  | succ order induction =>
    have unique : UniqueDiffOn ℝ (domain ×ˢ originalOpenCollar) :=
      (openDomain.prod originalOpenCollar_isOpen).uniqueDiffOn
    rw [Nat.cast_add,Nat.cast_one,contDiffOn_succ_iff_fderiv_apply unique]
    refine ⟨?_, by simp, fun direction => ?_⟩
    · intro point member
      exact (originalJointDerivative_hasFDerivAt parameters openDomain spatialOrder field smooth point member).differentiableAt.differentiableWithinAt
    · have parameterSmooth := induction spatialOrder
        (originalParameterDirectionField parameters openDomain field smooth direction.1)
        (originalParameterDirectionField_completed_smooth parameters openDomain field smooth direction.1)
      have spatialSmooth := (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (spatialOrder+1) => SpatialCell) (ComplexEuclidean dimension)).contDiff.comp_contDiffOn
          (induction (spatialOrder+1) field smooth)
      have sumSmooth := parameterSmooth.add (spatialSmooth.clm_apply (contDiffOn_const (c := direction.2)))
      apply sumSmooth.congr
      intro point member
      rw [(originalJointDerivative_hasFDerivAt parameters openDomain spatialOrder field smooth point member).hasFDerivWithinAt.fderivWithin (unique point member)]
      change originalClampedParameterDerivative parameters spatialOrder field point.1 point.2 direction.1 +
        (originalClampedDerivative parameters (spatialOrder+1) (field point.1) point.2).curryLeft direction.2=_
      rw [originalClampedParameterDerivative_direction parameters openDomain spatialOrder field smooth point.1 member.1 point.2 direction.1]
      rfl

theorem originalClampedDerivative_joint_contDiffOn
    {domain : Set Parameter} (openDomain : IsOpen domain) (spatialOrder : ℕ)
    (field : Parameter → ACore parameters dimension)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (completedCoreBranch parameters field grade) domain) :
    ContDiffOn ℝ ∞ (fun point : Parameter × SpatialCell =>
      originalClampedDerivative parameters spatialOrder (field point.1) point.2)
      (domain ×ˢ originalOpenCollar) :=
  contDiffOn_infty.mpr (fun order =>
    originalClampedDerivative_joint_contDiffOn_nat parameters openDomain order spatialOrder field smooth)

/-- Every spatial derivative of the actual P09 extension is jointly smooth
in the finite input and spatial variables on the single radius-4/3 collar. -/
theorem originalExtendedDerivative_joint_contDiffOn
    {domain : Set Parameter} (openDomain : IsOpen domain) (spatialOrder : ℕ)
    (field : Parameter → ACore parameters dimension)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (completedCoreBranch parameters field grade) domain) :
    ContDiffOn ℝ ∞ (fun point : Parameter × SpatialCell =>
      iteratedFDeriv ℝ spatialOrder (originalExtendedField parameters (field point.1)) point.2)
      (domain ×ˢ originalOpenCollar) := by
  apply (originalClampedDerivative_joint_contDiffOn parameters openDomain spatialOrder field smooth).congr
  intro point member
  rw [originalClampedDerivative_same parameters spatialOrder (field point.1) point.2 member.2,
    ambientHigherDerivative_eq_iteratedFDeriv_ambient]
  rfl

/-- SAME original field, SAME analytic width, one fixed collar, jointly C∞. -/
theorem originalExtendedField_joint_contDiffOn
    {domain : Set Parameter} (openDomain : IsOpen domain)
    (field : Parameter → ACore parameters dimension)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (completedCoreBranch parameters field grade) domain) :
    ContDiffOn ℝ ∞ (fun point : Parameter × SpatialCell =>
      originalExtendedField parameters (field point.1) point.2)
      (domain ×ˢ originalOpenCollar) := by
  have composed := (continuousMultilinearCurryFin0 ℝ SpatialCell (ComplexEuclidean dimension)).contDiff.comp_contDiffOn
    (originalClampedDerivative_joint_contDiffOn parameters openDomain 0 field smooth)
  apply composed.congr
  intro point member
  change originalExtendedField parameters (field point.1) point.2=
    (originalClampedDerivative parameters 0 (field point.1) point.2).curry0
  rw [originalClampedDerivative_same parameters 0 (field point.1) point.2 member.2,
    ambientHigherDerivative_zero_curry]
  rfl

end Grad.OriginalParameterEvaluation
