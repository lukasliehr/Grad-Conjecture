import AKCW3OriginalParameterDerivativeCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set
open scoped ContDiff Topology
namespace Grad.OriginalParameterEvaluation
open Grad.CartesianState

variable {dimension : ℕ} (parameters : PhaseParameters)
variable {Parameter : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]

/-- Each smooth completed branch supplies its actual derivative at points of
the one fixed open parameter set. -/
theorem completedCoreBranch_differentiableAt {domain : Set Parameter}
    (openDomain : IsOpen domain) (field : Parameter → ACore parameters dimension)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (completedCoreBranch parameters field grade) domain)
    (point : Parameter) (member : point ∈ domain) (grade : ℕ) :
    DifferentiableAt ℝ (completedCoreBranch parameters field grade) point :=
  ((smooth grade).contDiffAt (openDomain.mem_nhds member)).differentiableAt (by simp)

/-- The original-core directional derivative, extended by zero only outside
the parameter set where derivatives are used. -/
def originalParameterDirectionField {domain : Set Parameter}
    (openDomain : IsOpen domain) (field : Parameter → ACore parameters dimension)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (completedCoreBranch parameters field grade) domain)
    (direction : Parameter) (point : Parameter) : ACore parameters dimension := by
  classical
  exact if member : point ∈ domain then
    originalParameterDerivative parameters field point
      (completedCoreBranch_differentiableAt parameters openDomain field smooth point member) direction
    else 0

theorem originalParameterDirectionField_component {domain : Set Parameter}
    (openDomain : IsOpen domain) (field : Parameter → ACore parameters dimension)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (completedCoreBranch parameters field grade) domain)
    (direction point : Parameter) (member : point ∈ domain) (grade : ℕ) :
    completedCoreBranch parameters
      (originalParameterDirectionField parameters openDomain field smooth direction) grade point=
      fderiv ℝ (completedCoreBranch parameters field grade) point direction := by
  unfold completedCoreBranch originalParameterDirectionField
  rw [dif_pos member]
  exact originalParameterDerivative_component parameters field point _ grade direction

/-- Every directional derivative remains one original core and is smooth in
all the original completions on the SAME parameter domain. -/
theorem originalParameterDirectionField_completed_smooth {domain : Set Parameter}
    (openDomain : IsOpen domain) (field : Parameter → ACore parameters dimension)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (completedCoreBranch parameters field grade) domain)
    (direction : Parameter) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedCoreBranch parameters
      (originalParameterDirectionField parameters openDomain field smooth direction) grade) domain := by
  have derivativeSmooth := ((contDiffOn_infty_iff_fderiv_of_isOpen openDomain).mp (smooth grade)).2
  exact (derivativeSmooth.clm_apply contDiffOn_const).congr
    (fun point member => originalParameterDirectionField_component parameters openDomain field smooth direction point member grade)

/-- Finite-dimensional parameter smoothness transfers from all completions
to each literal original norm, using reconstructed original derivatives. -/
theorem originalCoreBranch_contDiffOn_nat [FiniteDimensional ℝ Parameter]
    {domain : Set Parameter} (openDomain : IsOpen domain) (order : ℕ)
    (field : Parameter → ACore parameters dimension)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (completedCoreBranch parameters field grade) domain)
    (grade : ℕ) :
    ContDiffOn ℝ order (fun point => GradeCore.ofCoreLinear (grade := grade) (field point)) domain := by
  induction order generalizing field with
  | zero =>
    apply contDiffOn_zero.mpr
    intro point member
    exact (originalParameterDerivative_hasFDerivAt parameters field point
      (completedCoreBranch_differentiableAt parameters openDomain field smooth point member) grade).continuousAt.continuousWithinAt
  | succ order induction =>
    rw [show ((order+1 : ℕ) : ℕ∞ω)=(order : ℕ∞ω)+1 by simp]
    apply contDiffOn_succ_of_fderiv_apply
    · intro point member
      exact (originalParameterDerivative_hasFDerivAt parameters field point
        (completedCoreBranch_differentiableAt parameters openDomain field smooth point member) grade).differentiableAt.differentiableWithinAt
    · intro impossible
      simp at impossible
    · intro direction
      have derivativeSmooth := induction
        (originalParameterDirectionField parameters openDomain field smooth direction)
        (originalParameterDirectionField_completed_smooth parameters openDomain field smooth direction)
      apply derivativeSmooth.congr
      intro point member
      have derivative := originalParameterDerivative_hasFDerivAt parameters field point
        (completedCoreBranch_differentiableAt parameters openDomain field smooth point member) grade
      rw [derivative.hasFDerivWithinAt.fderivWithin (openDomain.uniqueDiffOn point member)]
      unfold originalParameterDirectionField
      rw [dif_pos member]
      rfl

theorem originalCoreBranch_contDiffOn [FiniteDimensional ℝ Parameter]
    {domain : Set Parameter} (openDomain : IsOpen domain)
    (field : Parameter → ACore parameters dimension)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (completedCoreBranch parameters field grade) domain)
    (grade : ℕ) :
    ContDiffOn ℝ ∞ (fun point => GradeCore.ofCoreLinear (grade := grade) (field point)) domain :=
  contDiffOn_infty.mpr (fun order => originalCoreBranch_contDiffOn_nat parameters openDomain order field smooth grade)

end Grad.OriginalParameterEvaluation
