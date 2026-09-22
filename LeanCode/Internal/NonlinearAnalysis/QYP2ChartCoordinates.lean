import QYP1CompletedCoordinates
import Q24MixedMap

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 100000

namespace Grad.PhysicalCoordinates

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.Q24Realization Grad.ConstrainedGrades Grad.AxisCore Grad.ImplementationReadiness
open Grad.SmoothingFamily

def stateVectorMap {A V S : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup S] [NormedSpace ℂ S] (mapping : V →L[ℂ] V) :
    StateAmbient A V S →L[ℂ] StateAmbient A V S :=
  (WithLp.prodContinuousLinearEquiv 1 ℂ A (WithLp 1 (V × S))).symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.id ℂ A).prodMap
      ((WithLp.prodContinuousLinearEquiv 1 ℂ V S).symm.toContinuousLinearMap.comp
        ((mapping.prodMap (ContinuousLinearMap.id ℂ S)).comp
          (WithLp.prodContinuousLinearEquiv 1 ℂ V S).toContinuousLinearMap))).comp
      (WithLp.prodContinuousLinearEquiv 1 ℂ A (WithLp 1 (V × S))).toContinuousLinearMap)

theorem stateVectorMap_apply {A V S : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup S] [NormedSpace ℂ S] (mapping : V →L[ℂ] V)
    (state : StateAmbient A V S) :
    stateVectorMap mapping state =
      statePack state.ofLp.1 (mapping state.ofLp.2.ofLp.1) state.ofLp.2.ofLp.2 := rfl

theorem stateVectorMap_norm {A V S : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup S] [NormedSpace ℂ S] (mapping : V →L[ℂ] V)
    (isometry : ∀ vector, ‖mapping vector‖ = ‖vector‖)
    (state : StateAmbient A V S) :
    ‖stateVectorMap mapping state‖ = ‖state‖ := by
  rw [stateVectorMap_apply, statePack_norm, isometry,
    WithLp.prod_norm_eq_of_L1 state]
  change _ = ‖state.ofLp.1‖ + ‖state.ofLp.2‖
  rw [WithLp.prod_norm_eq_of_L1 state.ofLp.2]
  exact add_assoc _ _ _

/-- Intermediate chart isometry, with no claim that the legacy gauge slice is unchanged. -/
def chartVectorToPhysicalGrade (parameters : PhaseParameters) (grade : ℕ) :
    XAmbient parameters grade →L[ℂ] XAmbient parameters grade :=
  stateVectorMap (toPhysicalGrade parameters grade)

theorem chartVectorToPhysicalGrade_norm (parameters : PhaseParameters) (grade : ℕ)
    (state : XAmbient parameters grade) :
    ‖chartVectorToPhysicalGrade parameters grade state‖ = ‖state‖ :=
  stateVectorMap_norm (toPhysicalGrade parameters grade)
    (toPhysicalGrade_norm parameters grade) state

theorem chartVectorToPhysicalGrade_axis (parameters : PhaseParameters) (grade : ℕ)
    (state : XAmbient parameters grade) :
    (chartVectorToPhysicalGrade parameters grade state).ofLp.1 = state.ofLp.1 := rfl

theorem chartVectorToPhysicalGrade_core (parameters : PhaseParameters) (grade : ℕ)
    (state : ChartState parameters) :
    chartVectorToPhysicalGrade parameters grade (chartCoreEmbed parameters grade state) =
      chartCoreEmbed parameters grade (state.1, toPhysicalCore parameters state.2.1, state.2.2) := by
  apply (WithLp.equiv 1 _).injective
  apply Prod.ext
  · rfl
  · apply (WithLp.equiv 1 _).injective
    exact Prod.ext (toPhysicalGrade_core parameters grade state.2.1) rfl

theorem chartVectorToPhysicalGrade_domain_iff (parameters : PhaseParameters) (grade : ℕ)
    (state : XAmbient parameters grade) :
    chartVectorToPhysicalGrade parameters grade state ∈ chartDomain parameters grade ↔
      state ∈ chartDomain parameters grade := Iff.rfl

theorem chartVectorToPhysicalGrade_lowering {lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (state : XAmbient parameters upper) :
    xLowering parameters ordered (chartVectorToPhysicalGrade parameters upper state) =
      chartVectorToPhysicalGrade parameters lower (xLowering parameters ordered state) := by
  apply (WithLp.equiv 1 _).injective
  apply Prod.ext
  · rfl
  · apply (WithLp.equiv 1 _).injective
    exact Prod.ext (toPhysicalGrade_lowering parameters ordered state.ofLp.2.ofLp.1) rfl

end Grad.PhysicalCoordinates
