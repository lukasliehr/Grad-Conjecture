import COR13Realization

noncomputable section

namespace Grad.COR13Completion

open Grad.ClosedJets Grad.CartesianState Grad.FourierGrade Grad.COR12Extension

/-- The completed maps retain the exact COR12 composites on both dense
cores, all phase parameters, the same grade, and the original norm. -/
def ExactExtensionGoal : Prop :=
  ∀ dimension grade (parameters : PhaseParameters),
    (∀ field : GradeCore parameters dimension grade,
      completedExtension parameters (aGradeEta parameters field) =
        coreToGrade grade (weightedFourierExtension parameters field.toCore)) ∧
    (∀ values : JCore (ComplexEuclidean dimension),
      completedRetraction parameters (coreToGrade grade values) =
        aGradeEta parameters (GradeCore.ofCoreLinear
          (weightedFourierRetraction parameters values))) ∧
    ‖completedExtension (dimension := dimension) (grade := grade) parameters‖ ≤
      sameGradeConstant grade ∧
    ‖completedRetraction (dimension := dimension) (grade := grade) parameters‖ ≤
      sameGradeConstant grade

/-- The constructed extension/retraction yields a bounded idempotent on
the literal Fourier grade; no projection is included as an assumption. -/
def CompletedRetractGoal : Prop :=
  ∀ dimension grade (parameters : PhaseParameters),
    (completedRetraction parameters).comp (completedExtension parameters) =
      ContinuousLinearMap.id ℂ (AGrade parameters dimension grade) ∧
    (realizationProjection parameters).comp (realizationProjection parameters) =
      realizationProjection (dimension := dimension) (grade := grade) parameters ∧
    ‖realizationProjection (dimension := dimension) (grade := grade) parameters‖ ≤
      (sameGradeConstant grade) ^ 2

/-- The actual fixed subspace is closed and equals the range of the
completed extension, with its constructed two-sided bounded equivalence. -/
def ClosedRealizationGoal : Prop :=
  ∀ dimension grade (parameters : PhaseParameters),
    IsClosed (fixedRealization (dimension := dimension) (grade := grade) parameters).carrier ∧
    fixedRealization parameters =
      (completedExtension (dimension := dimension) (grade := grade) parameters).range ∧
    (∀ field : AGrade parameters dimension grade,
      (completedRealizationEquiv parameters field).1 = completedExtension parameters field) ∧
    (∀ values : fixedRealization (dimension := dimension) (grade := grade) parameters,
      (completedRealizationEquiv parameters).symm values = completedRetraction parameters values) ∧
    ‖(completedRealizationEquiv (dimension := dimension) (grade := grade)
      parameters).toContinuousLinearMap‖ ≤ sameGradeConstant grade ∧
    ‖(completedRealizationEquiv (dimension := dimension) (grade := grade)
      parameters).symm.toContinuousLinearMap‖ ≤ sameGradeConstant grade

/-- Exact FA-COR13: extensions in the original completion norm, completed
retraction, bounded projection, and closed-range continuous-linear realization. -/
def BlockGoal : Prop := ExactExtensionGoal ∧ CompletedRetractGoal ∧ ClosedRealizationGoal

end Grad.COR13Completion
