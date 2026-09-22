import AKDP24ActualFixedCoreRankControls

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers

/-- A finite actual operator formula has one rank profile before every
coefficient state. This predicate is used only to assemble that formula. -/
def StartupUniformOriginalRank {State : Type*} {input output rank : ℕ} (parameters : PhaseParameters)
    (budget : State → ℝ) (kernel : State → StartupL2 input →L[ℂ] StartupL2 output)
    (ranked : State → StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension output rank)) : Prop :=
  ∃ profile : StartupCoreRankProfile,∀ state,Nonempty (StartupCoreRankControl parameters (budget state) profile (kernel state) (ranked state))

namespace StartupUniformOriginalRank
variable {State : Type*} {input middle output rank : ℕ} {parameters : PhaseParameters} {budget : State → ℝ}

theorem add {firstKernel secondKernel : State → StartupL2 input →L[ℂ] StartupL2 output}
    {firstRank secondRank : State → StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension output rank)}
    (first : StartupUniformOriginalRank parameters budget firstKernel firstRank)
    (second : StartupUniformOriginalRank parameters budget secondKernel secondRank) :
    StartupUniformOriginalRank parameters budget (fun state => firstKernel state+secondKernel state)
      (fun state => firstRank state+secondRank state) := by
  obtain ⟨one,first⟩ := first
  obtain ⟨two,second⟩ := second
  refine ⟨one.sum two,fun state => ?_⟩
  exact ⟨(first state).some.add (second state).some⟩

theorem sub {firstKernel secondKernel : State → StartupL2 input →L[ℂ] StartupL2 output}
    {firstRank secondRank : State → StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension output rank)}
    (first : StartupUniformOriginalRank parameters budget firstKernel firstRank)
    (second : StartupUniformOriginalRank parameters budget secondKernel secondRank) :
    StartupUniformOriginalRank parameters budget (fun state => firstKernel state-secondKernel state)
      (fun state => firstRank state-secondRank state) := by
  obtain ⟨one,first⟩ := first
  obtain ⟨two,second⟩ := second
  refine ⟨one.sum two,fun state => ?_⟩
  exact ⟨(first state).some.sub (second state).some⟩

theorem comp {outerKernel : State → StartupL2 middle →L[ℂ] StartupL2 output}
    {innerKernel : State → StartupL2 input →L[ℂ] StartupL2 middle}
    {outerRank : State → StartupL2 (startupTensorDimension middle rank) →L[ℂ] StartupL2 (startupTensorDimension output rank)}
    {innerRank : State → StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension middle rank)}
    (outer : StartupUniformOriginalRank parameters budget outerKernel outerRank)
    (inner : StartupUniformOriginalRank parameters budget innerKernel innerRank)
    (outerBound : ℝ) (nonnegative : 0≤outerBound) (bounded : ∀ state,‖outerRank state‖≤outerBound)
    (budgetNonnegative : ∀ state,0≤budget state) :
    StartupUniformOriginalRank parameters budget (fun state => (outerKernel state).comp (innerKernel state))
      (fun state => (outerRank state).comp (innerRank state)) := by
  obtain ⟨one,outer⟩ := outer
  obtain ⟨two,inner⟩ := inner
  refine ⟨one.composition two outerBound nonnegative,fun state => ?_⟩
  exact ⟨(outer state).some.comp (inner state).some outerBound nonnegative (bounded state) (budgetNonnegative state)⟩

theorem identity (dimension rank : ℕ) (budgetNonnegative : ∀ state,0≤budget state) :
    StartupUniformOriginalRank parameters budget (fun _ => ContinuousLinearMap.id ℂ (StartupL2 dimension))
      (fun _ => (StartupRankOperator.identity rank dimension).coarse) :=
  ⟨StartupCoreRankProfile.fixed 1 1 zero_le_one zero_le_one,fun state => ⟨StartupCoreRankControl.identity dimension rank (budgetNonnegative state)⟩⟩

theorem smul {kernel : State → StartupL2 input →L[ℂ] StartupL2 output}
    {ranked : State → StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension output rank)}
    (actual : StartupUniformOriginalRank parameters budget kernel ranked) (scalar : ℂ)
    (budgetNonnegative : ∀ state,0≤budget state) :
    StartupUniformOriginalRank parameters budget (fun state => scalar • kernel state) (fun state => scalar • ranked state) := by
  have fixed : StartupUniformOriginalRank parameters budget
      (fun _ => scalar • ContinuousLinearMap.id ℂ (StartupL2 output))
      (fun _ => ((StartupRankOperator.identity rank output).smul scalar).coarse) :=
    ⟨StartupCoreRankProfile.fixed ‖scalar‖ ‖scalar‖ (norm_nonneg _) (norm_nonneg _),fun state =>
      ⟨StartupCoreRankControl.scalar output rank scalar (budgetNonnegative state)⟩⟩
  have composed := fixed.comp actual ‖scalar‖ (norm_nonneg _) (fun _ => by
    change ‖scalar • ContinuousLinearMap.id ℂ (StartupL2 (startupTensorDimension output rank))‖≤‖scalar‖
    rw [norm_smul]
    have identityBound : ‖ContinuousLinearMap.id ℂ (StartupL2 (startupTensorDimension output rank))‖≤1 := ContinuousLinearMap.norm_id_le
    exact (mul_le_mul_of_nonneg_left identityBound (norm_nonneg scalar)).trans_eq (mul_one _))
    budgetNonnegative
  simpa only [StartupRankOperator.smul,StartupRankOperator.identity,ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.id_comp] using composed

end StartupUniformOriginalRank
end Grad.CartesianStartup
