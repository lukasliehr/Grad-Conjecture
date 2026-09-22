import COR16Topology

noncomputable section

namespace Grad.CompatibleCompletion

open Grad.ClosedJets Grad.CartesianState Grad.FourierGrade Grad.COR12Extension Grad.COR13Completion

/-- Exact FA-COR14, including endpoints of both P29 identities and the
constant-one map between the actual original norm completions. -/
def CompletedInclusionGoal : Prop :=
  (∀ dimension lower upper (parameters : PhaseParameters) (ordered : lower ≤ upper),
    ‖completedInclusion (dimension := dimension) parameters ordered‖ ≤ 1 ∧
    (∀ field : GradeCore parameters dimension upper,
      completedInclusion parameters ordered (aGradeEta parameters field) =
        aGradeEta parameters (GradeCore.ofCoreLinear field.toCore)) ∧
    (completedExtension (dimension := dimension) (grade := lower) parameters).comp
      (completedInclusion parameters ordered) =
        (inclusion upper lower ordered).comp (completedExtension parameters) ∧
    (completedInclusion (dimension := dimension) parameters ordered).comp
      (completedRetraction parameters) =
        (completedRetraction parameters).comp (inclusion upper lower ordered)) ∧
  (∀ dimension grade (parameters : PhaseParameters),
    completedInclusion parameters (le_refl grade) =
      ContinuousLinearMap.id ℂ (AGrade parameters dimension grade)) ∧
  (∀ dimension high middle low (parameters : PhaseParameters)
    (middleHigh : middle ≤ high) (lowMiddle : low ≤ middle),
    (completedInclusion (dimension := dimension) parameters lowMiddle).comp
      (completedInclusion parameters middleHigh) =
        completedInclusion parameters (lowMiddle.trans middleHigh))

/-- Exact FA-COR15: injectivity is on completed grades, not just smooth inputs. -/
def CompletedInjectivityGoal : Prop :=
  ∀ dimension lower upper (parameters : PhaseParameters) (ordered : lower ≤ upper),
    Function.Injective (completedInclusion (dimension := dimension) parameters ordered)

/-- Exact FA-COR16: one smooth original field represents an arbitrary
compatible family, with both inverse laws, exact component norms and the
same original seminorm-family topology. -/
def SmoothCompatibleLimitGoal : Prop :=
  ∀ dimension (parameters : PhaseParameters),
    (∀ field : ACore parameters dimension,
      compatibleToCore parameters (coreToCompatible parameters field) = field) ∧
    (∀ family : CompatibleAGrades parameters dimension,
      coreToCompatible parameters (compatibleToCore parameters family) = family) ∧
    (∀ (field : ACore parameters dimension) (grade : ℕ),
      ‖(coreCompatibleEquiv parameters field).1 grade‖ =
        cartesianGradeSeminorm parameters (GradeCore.ofCoreLinear (grade := grade) field)) ∧
    (∀ field : ACore parameters dimension,
      coreCompatibleHomeomorph parameters field = coreCompatibleEquiv parameters field) ∧
    originalGradedTopology parameters dimension =
      TopologicalSpace.induced (coreToCompatible (dimension := dimension) parameters) inferInstance

/-- The coherent completion-compatibility block FA-COR14 through FA-COR16. -/
def BlockGoal : Prop :=
  CompletedInclusionGoal ∧ CompletedInjectivityGoal ∧ SmoothCompatibleLimitGoal

end Grad.CompatibleCompletion
