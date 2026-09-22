import AKDP25UniformActualRankComposition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.Constraints
open Grad.GaugeCoefficients.Algebra

/-- Reindexing changes neither the selected constants nor the actual action. -/
theorem StartupUniformOriginalRank.reindex {State Other : Type*} {input output rank : ℕ}
    {parameters : PhaseParameters} {budget : State → ℝ}
    {kernel : State → StartupL2 input →L[ℂ] StartupL2 output}
    {ranked : State → StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension output rank)}
    (actual : StartupUniformOriginalRank parameters budget kernel ranked) (index : Other → State) :
    StartupUniformOriginalRank parameters (budget ∘ index) (kernel ∘ index) (ranked ∘ index) := by
  obtain ⟨profile,controlled⟩ := actual
  exact ⟨profile,fun state => controlled (index state)⟩

namespace StartupSpatialAction
variable {L ell : ℝ} {input middle output rank : ℕ} {parameters : PhaseParameters}

def OriginalRankControlled (parameters : PhaseParameters) (operator : StartupSpatialAction rank input output L ell) : Prop :=
  StartupUniformOriginalRank parameters (fun budget : {value : ℝ // 0≤value} => budget.val)
    (fun _ => operator.signed.coarse) (fun _ => operator.ranked.coarse)

namespace OriginalRankControlled

theorem onBudget {State : Type*} {operator : StartupSpatialAction rank input output L ell}
    (actual : operator.OriginalRankControlled parameters) (budget : State → ℝ) (nonnegative : ∀ state,0≤budget state) :
    StartupUniformOriginalRank parameters budget (fun _ => operator.signed.coarse) (fun _ => operator.ranked.coarse) :=
  actual.reindex (fun state => ⟨budget state,nonnegative state⟩)

theorem comp {outer : StartupSpatialAction rank middle output L ell} {inner : StartupSpatialAction rank input middle L ell}
    (one : outer.OriginalRankControlled parameters) (two : inner.OriginalRankControlled parameters) :
    (outer.comp inner).OriginalRankControlled parameters :=
  StartupUniformOriginalRank.comp one two outer.ranked.bound outer.ranked.nonnegative (fun _ => outer.ranked.coarse_bound) (fun budget => budget.property)

theorem add {first second : StartupSpatialAction rank input output L ell}
    (one : first.OriginalRankControlled parameters) (two : second.OriginalRankControlled parameters) :
    (first.add second).OriginalRankControlled parameters := StartupUniformOriginalRank.add one two

theorem sub {first second : StartupSpatialAction rank input output L ell}
    (one : first.OriginalRankControlled parameters) (two : second.OriginalRankControlled parameters) :
    (first.sub second).OriginalRankControlled parameters := StartupUniformOriginalRank.sub one two

theorem smul {operator : StartupSpatialAction rank input output L ell}
    (actual : operator.OriginalRankControlled parameters) (scalar : ℂ) :
    (operator.smul scalar).OriginalRankControlled parameters := StartupUniformOriginalRank.smul actual scalar (fun budget => budget.property)

end OriginalRankControlled

theorem identity_originalRankControlled (parameters : PhaseParameters) (rank dimension : ℕ) :
    (identity (L := L) (ell := ell) rank dimension).OriginalRankControlled parameters :=
  StartupUniformOriginalRank.identity dimension rank (fun budget => budget.property)

theorem point_originalRankControlled (parameters : PhaseParameters) (rank : ℕ)
    (mapping : OperatorValue input output) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) :
    (point (L := L) (ell := ell) rank mapping orthogonal).OriginalRankControlled parameters := by
  refine ⟨StartupCoreRankProfile.fixed (‖mapping‖*orthogonalGradeConstant 0) (‖mapping‖*orthogonalGradeConstant rank)
    (mul_nonneg (norm_nonneg _) (orthogonalGradeConstant_nonnegative _))
    (mul_nonneg (norm_nonneg _) (orthogonalGradeConstant_nonnegative _)),?_⟩
  intro budget
  exact ⟨StartupCoreRankControl.point input output rank mapping orthogonal budget.property⟩

theorem angular_originalRankControlled (parameters : PhaseParameters) (dimension rank : ℕ)
    (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight) :
    (angular (L := L) (ell := ell) dimension rank weight smooth).OriginalRankControlled parameters := by
  obtain ⟨bound,bounded⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2*Real.pi))).exists_bound_of_continuousOn smooth.continuous.continuousOn
  have positiveBound : 0≤|bound| := abs_nonneg bound
  have dominated : ∀ angle ∈ Icc (0 : ℝ) (2*Real.pi),‖weight angle‖≤|bound| :=
    fun angle inside => (bounded angle inside).trans (le_abs_self bound)
  refine ⟨StartupCoreRankProfile.fixed (|bound| *orthogonalGradeConstant 0) (|bound| *orthogonalGradeConstant rank)
    (mul_nonneg positiveBound (orthogonalGradeConstant_nonnegative _))
    (mul_nonneg positiveBound (orthogonalGradeConstant_nonnegative _)),?_⟩
  intro budget
  exact ⟨StartupCoreRankControl.angular dimension rank weight smooth |bound| positiveBound dominated budget.property⟩

end StartupSpatialAction
end Grad.CartesianStartup
