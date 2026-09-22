import QV4ConstrainedEquivalence
import Mathlib.Analysis.LocallyConvex.WithSeminorms

noncomputable section

namespace Grad.ConstrainedGrades

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.SmoothingFamily Grad.AxisCore Grad.QuotientProjection

/-- Every original state-grade seminorm, including grades 0,1,2 and the
literal shifted axis norm. No topology is defined through representatives. -/
def stateOriginalSeminorms (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) :
    SeminormFamily ℝ (stateSmoothRange parameters parameter inside) ℕ :=
  fun grade => (normSeminorm ℝ (XAmbient parameters grade)).comp
    (((stateToGrade parameters grade).restrictScalars ℝ).comp (stateSmoothRange parameters parameter inside).subtype)

def sourceOriginalSeminorms (parameters : PhaseParameters) :
    SeminormFamily ℝ (sourceSmoothRange parameters) ℕ :=
  fun grade => (normSeminorm ℝ (ZAmbient parameters grade)).comp
    (((quotientEta parameters grade).restrictScalars ℝ).comp (sourceSmoothRange parameters).subtype)

theorem stateOriginalSeminorms_apply (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (field : stateSmoothRange parameters parameter inside) :
    stateOriginalSeminorms parameters parameter inside grade field = ‖stateToGrade parameters grade field.val‖ := rfl

theorem sourceOriginalSeminorms_apply (parameters : PhaseParameters) (grade : ℕ)
    (field : sourceSmoothRange parameters) :
    sourceOriginalSeminorms parameters grade field = quotientNorm parameters grade field.val := rfl

abbrev stateOriginalTopology (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) : TopologicalSpace (stateSmoothRange parameters parameter inside) :=
  (stateOriginalSeminorms parameters parameter inside).moduleFilterBasis.topology

abbrev sourceOriginalTopology (parameters : PhaseParameters) : TopologicalSpace (sourceSmoothRange parameters) :=
  (sourceOriginalSeminorms parameters).moduleFilterBasis.topology

theorem stateOriginalTopology_withSeminorms (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) :
    WithSeminorms (topology := stateOriginalTopology parameters parameter inside)
      (stateOriginalSeminorms parameters parameter inside) := by
  let _ := stateOriginalTopology parameters parameter inside
  exact ⟨rfl⟩

theorem sourceOriginalTopology_withSeminorms (parameters : PhaseParameters) :
    WithSeminorms (topology := sourceOriginalTopology parameters) (sourceOriginalSeminorms parameters) := by
  let _ := sourceOriginalTopology parameters
  exact ⟨rfl⟩

/-- Continuous coordinate in every ambient grade, using the canonical
inclusion from max(q,3). Thus the omitted low seminorms are also controlled. -/
def extendedStateCoordinate (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) :
    CompatibleStates parameters parameter inside →L[ℝ] XAmbient parameters grade :=
  ((xLowering parameters (le_max_left grade 3)).restrictScalars ℝ).comp
    ((stateInclusion parameters parameter inside (max grade 3) (le_max_right grade 3)).comp
      (compatibleStateCoordinate parameters parameter inside ⟨max grade 3, le_max_right grade 3⟩))

def extendedSourceCoordinate (parameters : PhaseParameters) (grade : ℕ) :
    CompatibleSources parameters →L[ℝ] ZAmbient parameters grade :=
  ((zLowering parameters (le_max_left grade 3)).restrictScalars ℝ).comp
    ((sourceInclusion parameters (max grade 3) (le_max_right grade 3)).comp
      (compatibleSourceCoordinate parameters ⟨max grade 3, le_max_right grade 3⟩))

theorem extendedStateCoordinate_apply (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (family : CompatibleStates parameters parameter inside) :
    extendedStateCoordinate parameters parameter inside grade family = extendedState parameters parameter inside family grade := rfl

theorem extendedSourceCoordinate_apply (parameters : PhaseParameters) (grade : ℕ) (family : CompatibleSources parameters) :
    extendedSourceCoordinate parameters grade family = extendedSource parameters family grade := rfl

theorem stateCompatibleEquiv_original_norm (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : stateSmoothRange parameters parameter inside)
    (grade : AdmissibleGrade) :
    ‖(stateCompatibleEquiv parameters parameter inside field).val grade‖ =
      stateOriginalSeminorms parameters parameter inside grade.val field := rfl

theorem sourceCompatibleEquiv_original_norm (parameters : PhaseParameters)
    (field : sourceSmoothRange parameters) (grade : AdmissibleGrade) :
    ‖(sourceCompatibleEquiv parameters field).val grade‖ = sourceOriginalSeminorms parameters grade.val field := rfl

end Grad.ConstrainedGrades
