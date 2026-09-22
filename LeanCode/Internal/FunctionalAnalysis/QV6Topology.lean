import QV5OriginalSeminorms

noncomputable section

set_option maxHeartbeats 400000

namespace Grad.ConstrainedGrades

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.SmoothingFamily Grad.AxisCore

/-- Continuity detected by the target norm, with all source structures
explicit at concrete subtype applications. -/
theorem linearContinuous_of_normContinuous {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (linear : E →ₗ[ℝ] F) (normContinuous : Continuous (fun field => ‖linear field‖)) :
    Continuous linear :=
  (norm_withSeminorms ℝ F).continuous_of_continuous_comp linear (fun _ => normContinuous)

theorem continuous_stateToCompatible (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) :
    @Continuous (stateSmoothRange parameters parameter inside) (CompatibleStates parameters parameter inside)
      (stateOriginalTopology parameters parameter inside) inferInstance (stateToCompatible parameters parameter inside) := by
  let _ : TopologicalSpace (stateSmoothRange parameters parameter inside) := stateOriginalTopology parameters parameter inside
  have sourceSeminorms := stateOriginalTopology_withSeminorms parameters parameter inside
  let _ : IsTopologicalAddGroup (stateSmoothRange parameters parameter inside) := sourceSeminorms.topologicalAddGroup
  apply Continuous.subtype_mk
  apply continuous_pi
  intro grade
  apply Continuous.subtype_mk
  let component : stateSmoothRange parameters parameter inside →ₗ[ℝ] XAmbient parameters grade.val :=
    ((stateToGrade parameters grade.val).restrictScalars ℝ).comp
      (stateSmoothRange parameters parameter inside).subtype
  change Continuous component
  have normContinuous : Continuous (fun field : stateSmoothRange parameters parameter inside => ‖component field‖) := by
    change Continuous (stateOriginalSeminorms parameters parameter inside grade.val)
    exact sourceSeminorms.continuous_seminorm grade.val
  exact @linearContinuous_of_normContinuous (stateSmoothRange parameters parameter inside)
    (XAmbient parameters grade.val) inferInstance inferInstance
    (stateOriginalTopology parameters parameter inside) sourceSeminorms.topologicalAddGroup
    inferInstance inferInstance component normContinuous

theorem continuous_sourceToCompatible (parameters : PhaseParameters) :
    @Continuous (sourceSmoothRange parameters) (CompatibleSources parameters)
      (sourceOriginalTopology parameters) inferInstance (sourceToCompatible parameters) := by
  let _ : TopologicalSpace (sourceSmoothRange parameters) := sourceOriginalTopology parameters
  have sourceSeminorms := sourceOriginalTopology_withSeminorms parameters
  let _ : IsTopologicalAddGroup (sourceSmoothRange parameters) := sourceSeminorms.topologicalAddGroup
  apply Continuous.subtype_mk
  apply continuous_pi
  intro grade
  apply Continuous.subtype_mk
  let component : sourceSmoothRange parameters →ₗ[ℝ] ZAmbient parameters grade.val :=
    ((Grad.QuotientProjection.quotientEta parameters grade.val).restrictScalars ℝ).comp
      (sourceSmoothRange parameters).subtype
  change Continuous component
  have normContinuous : Continuous (fun field : sourceSmoothRange parameters => ‖component field‖) := by
    change Continuous (sourceOriginalSeminorms parameters grade.val)
    exact sourceSeminorms.continuous_seminorm grade.val
  exact @linearContinuous_of_normContinuous (sourceSmoothRange parameters)
    (ZAmbient parameters grade.val) inferInstance inferInstance
    (sourceOriginalTopology parameters) sourceSeminorms.topologicalAddGroup
    inferInstance inferInstance component normContinuous

theorem continuous_stateCompatibleInverse (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) :
    @Continuous (CompatibleStates parameters parameter inside) (stateSmoothRange parameters parameter inside)
      inferInstance (stateOriginalTopology parameters parameter inside) (stateCompatibleEquiv parameters parameter inside).symm := by
  let _ := stateOriginalTopology parameters parameter inside
  have targetSeminorms := stateOriginalTopology_withSeminorms parameters parameter inside
  change Continuous (stateCompatibleEquiv parameters parameter inside).symm.toLinearMap
  apply targetSeminorms.continuous_of_continuous_comp
  intro grade
  have normEquality : (stateOriginalSeminorms parameters parameter inside grade).comp
      (stateCompatibleEquiv parameters parameter inside).symm.toLinearMap =
      (normSeminorm ℝ (XAmbient parameters grade)).comp
        (extendedStateCoordinate parameters parameter inside grade).toLinearMap := by
    apply DFunLike.ext
    intro family
    change ‖stateToGrade parameters grade ((stateCompatibleEquiv parameters parameter inside).symm family).val‖ =
      ‖extendedState parameters parameter inside family grade‖
    rw [stateCompatibleEquiv_inverse_allGrades]
  rw [normEquality]
  exact (extendedStateCoordinate parameters parameter inside grade).continuous.norm

theorem continuous_sourceCompatibleInverse (parameters : PhaseParameters) :
    @Continuous (CompatibleSources parameters) (sourceSmoothRange parameters)
      inferInstance (sourceOriginalTopology parameters) (sourceCompatibleEquiv parameters).symm := by
  let _ := sourceOriginalTopology parameters
  have targetSeminorms := sourceOriginalTopology_withSeminorms parameters
  change Continuous (sourceCompatibleEquiv parameters).symm.toLinearMap
  apply targetSeminorms.continuous_of_continuous_comp
  intro grade
  have normEquality : (sourceOriginalSeminorms parameters grade).comp
      (sourceCompatibleEquiv parameters).symm.toLinearMap =
      (normSeminorm ℝ (ZAmbient parameters grade)).comp
        (extendedSourceCoordinate parameters grade).toLinearMap := by
    apply DFunLike.ext
    intro family
    change ‖Grad.QuotientProjection.quotientEta parameters grade
      ((sourceCompatibleEquiv parameters).symm family).val‖ = ‖extendedSource parameters family grade‖
    rw [sourceCompatibleEquiv_inverse_allGrades]
  rw [normEquality]
  exact (extendedSourceCoordinate parameters grade).continuous.norm

/-- The original seminorm-family topology is exactly the inherited
dependent-product topology under the actual linear reconstruction. -/
def stateCompatibleHomeomorph (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) :
    @Homeomorph (stateSmoothRange parameters parameter inside) (CompatibleStates parameters parameter inside)
      (stateOriginalTopology parameters parameter inside) inferInstance := by
  let _ := stateOriginalTopology parameters parameter inside
  exact { toEquiv := (stateCompatibleEquiv parameters parameter inside).toEquiv
          continuous_toFun := continuous_stateToCompatible parameters parameter inside
          continuous_invFun := continuous_stateCompatibleInverse parameters parameter inside }

def sourceCompatibleHomeomorph (parameters : PhaseParameters) :
    @Homeomorph (sourceSmoothRange parameters) (CompatibleSources parameters)
      (sourceOriginalTopology parameters) inferInstance := by
  let _ := sourceOriginalTopology parameters
  exact { toEquiv := (sourceCompatibleEquiv parameters).toEquiv
          continuous_toFun := continuous_sourceToCompatible parameters
          continuous_invFun := continuous_sourceCompatibleInverse parameters }

theorem stateOriginalTopology_eq_induced (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) :
    stateOriginalTopology parameters parameter inside =
      TopologicalSpace.induced (stateToCompatible parameters parameter inside) inferInstance := by
  let _ := stateOriginalTopology parameters parameter inside
  exact (stateCompatibleHomeomorph parameters parameter inside).isInducing.eq_induced

theorem sourceOriginalTopology_eq_induced (parameters : PhaseParameters) :
    sourceOriginalTopology parameters = TopologicalSpace.induced (sourceToCompatible parameters) inferInstance := by
  let _ := sourceOriginalTopology parameters
  exact (sourceCompatibleHomeomorph parameters).isInducing.eq_induced

end Grad.ConstrainedGrades
