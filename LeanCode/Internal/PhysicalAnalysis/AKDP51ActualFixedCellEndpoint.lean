import AKDP50ActualCellFiniteFormula

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.Constraints Grad.NonlinearProduct
open Grad.OriginalCartesianTameEstimate Grad.OriginalCoreRealization Grad.GaugeCoefficients.Algebra
namespace StartupUniformOriginalEndpoint

theorem fixed {State : Type*} {input output rank : ℕ} {parameters : PhaseParameters} {budget : State → ℝ}
    {kernel : StartupL2 input →L[ℂ] StartupL2 output}
    {ranked : StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension output rank)}
    (controlled : StartupUniformOriginalRank parameters budget (fun _ => kernel) (fun _ => ranked))
    (action : ACore parameters input → ACore parameters output)
    (same : ∀ core,originalSourceFieldLinear parameters (action core)=kernel (originalSourceFieldLinear parameters core))
    (constant : ℝ) (nonnegative : 0≤constant)
    (bounded : ∀ core,originalCellNorm parameters rank (action core)≤constant*originalCellNorm parameters rank core) :
    StartupUniformOriginalEndpoint parameters budget (fun _ => kernel) (fun _ => ranked) := by
  refine ⟨controlled,constant,nonnegative,?_⟩
  intro epsilon positive
  refine ⟨0,le_rfl,?_⟩
  intro state core image imageSame
  have identical : image=action core := originalSourceFieldLinear_injective parameters (imageSame.trans (same core).symm)
  rw [identical,zero_mul,add_zero]
  exact (bounded core).trans (le_add_of_nonneg_right (mul_nonneg positive.le (originalGradeNorm_nonnegative rank core)))

theorem reindex {State Other : Type*} {input output rank : ℕ}
    {parameters : PhaseParameters} {budget : State → ℝ}
    {kernel : State → StartupL2 input →L[ℂ] StartupL2 output}
    {ranked : State → StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension output rank)}
    (actual : StartupUniformOriginalEndpoint parameters budget kernel ranked) (index : Other → State) :
    StartupUniformOriginalEndpoint parameters (budget ∘ index) (kernel ∘ index) (ranked ∘ index) := by
  refine ⟨actual.1.reindex index,?_⟩
  obtain ⟨leading,nonnegative,bound⟩ := actual.2
  refine ⟨leading,nonnegative,?_⟩
  intro epsilon positive
  obtain ⟨tail,tailNonnegative,estimate⟩ := bound epsilon positive
  exact ⟨tail,tailNonnegative,fun state => estimate (index state)⟩

theorem smul {State : Type*} {input output rank : ℕ}
    {parameters : PhaseParameters} {budget : State → ℝ}
    {kernel : State → StartupL2 input →L[ℂ] StartupL2 output}
    {ranked : State → StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension output rank)}
    (actual : StartupUniformOriginalEndpoint parameters budget kernel ranked) (scalar : ℂ)
    (budgetNonnegative : ∀ state,0≤budget state) :
    StartupUniformOriginalEndpoint parameters budget (fun state => scalar • kernel state) (fun state => scalar • ranked state) := by
  refine ⟨actual.1.smul scalar budgetNonnegative,?_⟩
  obtain ⟨leading,nonnegative,bound⟩ := actual.2
  obtain ⟨_,controls⟩ := actual.1
  refine ⟨‖scalar‖*leading,mul_nonneg (norm_nonneg _) nonnegative,?_⟩
  intro epsilon positive
  let delta := epsilon/(‖scalar‖+1)
  have deltaPositive : 0<delta := div_pos positive (by positivity)
  obtain ⟨tail,tailNonnegative,estimate⟩ := bound delta deltaPositive
  refine ⟨‖scalar‖*tail,mul_nonneg (norm_nonneg _) tailNonnegative,?_⟩
  intro state core image same
  let one := (controls state).some
  have imageSame : image=scalar • one.action core := by
    apply originalSourceFieldLinear_injective parameters
    rw [map_smul,one.same]
    exact same
  rw [imageSame,startupOriginalCellNorm_smul]
  have paid := mul_le_mul_of_nonneg_left (estimate state core (one.action core) (one.same core)) (norm_nonneg scalar)
  have allocated : ‖scalar‖*delta≤epsilon := by
    have exactDelta : delta*(‖scalar‖+1)=epsilon := div_mul_cancel₀ epsilon (by positivity)
    nlinarith [deltaPositive]
  have main := mul_le_mul_of_nonneg_right allocated (originalGradeNorm_nonnegative rank core)
  nlinarith only [paid,main]

end StartupUniformOriginalEndpoint
namespace StartupSpatialAction
variable {L ell : ℝ} {input middle output rank : ℕ} {parameters : PhaseParameters}

def OriginalEndpointControlled (parameters : PhaseParameters) (operator : StartupSpatialAction rank input output L ell) : Prop :=
  StartupUniformOriginalEndpoint parameters (fun budget : {value : ℝ // 0≤value} => budget.val)
    (fun _ => operator.signed.coarse) (fun _ => operator.ranked.coarse)

namespace OriginalEndpointControlled
theorem onBudget {State : Type*} {operator : StartupSpatialAction rank input output L ell}
    (actual : operator.OriginalEndpointControlled parameters) (budget : State → ℝ) (nonnegative : ∀ state,0≤budget state) :
    StartupUniformOriginalEndpoint parameters budget (fun _ => operator.signed.coarse) (fun _ => operator.ranked.coarse) :=
  actual.reindex (fun state => ⟨budget state,nonnegative state⟩)
theorem comp {outer : StartupSpatialAction rank middle output L ell} {inner : StartupSpatialAction rank input middle L ell}
    (one : outer.OriginalEndpointControlled parameters) (two : inner.OriginalEndpointControlled parameters) :
    (outer.comp inner).OriginalEndpointControlled parameters :=
  StartupUniformOriginalEndpoint.comp one two outer.ranked.bound outer.ranked.nonnegative
    (fun _ => outer.ranked.coarse_bound) (fun budget => budget.property)
theorem add {first second : StartupSpatialAction rank input output L ell}
    (one : first.OriginalEndpointControlled parameters) (two : second.OriginalEndpointControlled parameters) :
    (first.add second).OriginalEndpointControlled parameters := StartupUniformOriginalEndpoint.add one two
theorem sub {first second : StartupSpatialAction rank input output L ell}
    (one : first.OriginalEndpointControlled parameters) (two : second.OriginalEndpointControlled parameters) :
    (first.sub second).OriginalEndpointControlled parameters := StartupUniformOriginalEndpoint.sub one two
theorem smul {operator : StartupSpatialAction rank input output L ell}
    (actual : operator.OriginalEndpointControlled parameters) (scalar : ℂ) :
    (operator.smul scalar).OriginalEndpointControlled parameters :=
  StartupUniformOriginalEndpoint.smul actual scalar (fun budget => budget.property)
end OriginalEndpointControlled

theorem identity_originalEndpointControlled (parameters : PhaseParameters) (rank dimension : ℕ) :
    (identity (L := L) (ell := ell) rank dimension).OriginalEndpointControlled parameters :=
  StartupUniformOriginalEndpoint.fixed (identity_originalRankControlled parameters rank dimension) id (fun _ => rfl)
    1 zero_le_one (fun _ => by simp only [id_eq,one_mul,le_refl])

theorem point_originalEndpointControlled (parameters : PhaseParameters) (rank : ℕ)
    (mapping : OperatorValue input output) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) :
    (point (L := L) (ell := ell) rank mapping orthogonal).OriginalEndpointControlled parameters :=
  StartupUniformOriginalEndpoint.fixed (point_originalRankControlled parameters rank mapping orthogonal)
    (startupOriginalPointCore parameters mapping orthogonal) (startupOriginalPointCore_sameField parameters mapping orthogonal)
    (‖mapping‖*orthogonalGradeConstant 0) (mul_nonneg (norm_nonneg _) (orthogonalGradeConstant_nonnegative 0))
    (fun core => startupOriginalPointCore_cell_bound parameters mapping orthogonal core rank)

theorem angular_originalEndpointControlled (parameters : PhaseParameters) (dimension rank : ℕ)
    (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight) :
    (angular (L := L) (ell := ell) dimension rank weight smooth).OriginalEndpointControlled parameters := by
  obtain ⟨bound,bounded⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2*Real.pi))).exists_bound_of_continuousOn smooth.continuous.continuousOn
  have nonnegative : 0≤|bound| := abs_nonneg bound
  have dominated : ∀ angle∈Icc (0 : ℝ) (2*Real.pi),‖weight angle‖≤|bound| :=
    fun angle inside => (bounded angle inside).trans (le_abs_self bound)
  exact StartupUniformOriginalEndpoint.fixed (angular_originalRankControlled parameters dimension rank weight smooth)
    (originalAngularKernelCore parameters weight smooth |bound| nonnegative dominated)
    (originalAngularKernelCore_sameField parameters weight smooth |bound| nonnegative dominated)
    (|bound| *orthogonalGradeConstant 0) (mul_nonneg nonnegative (orthogonalGradeConstant_nonnegative 0))
    (fun core => startupOriginalAngularCore_cell_bound parameters weight smooth |bound| nonnegative dominated core rank)

end StartupSpatialAction
end Grad.CartesianStartup
