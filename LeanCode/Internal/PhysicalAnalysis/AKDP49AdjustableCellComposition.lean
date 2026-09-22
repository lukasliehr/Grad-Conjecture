import AKDP48ActualFixedPureCellBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.NonlinearProduct
open Grad.OriginalCartesianTameEstimate Grad.OriginalCoreRealization

/-- Uniform actual pure-cell control with an adjustable full-norm term.
All constants are chosen before the coefficient state and input core. -/
def StartupUniformOriginalCell {State : Type*} {input output : ℕ}
    (parameters : PhaseParameters) (rank : ℕ) (budget : State → ℝ)
    (kernel : State → StartupL2 input →L[ℂ] StartupL2 output) : Prop :=
  ∃ leading : ℝ,0≤leading ∧ ∀ epsilon : ℝ,0<epsilon → ∃ remainder : ℝ,0≤remainder ∧
    ∀ (state : State) (core : ACore parameters input) (image : ACore parameters output),
      originalSourceFieldLinear parameters image=kernel state (originalSourceFieldLinear parameters core) →
      originalCellNorm parameters rank image≤leading*originalCellNorm parameters rank core+
        epsilon*originalGradeNorm rank core+remainder*(budget state*originalGradeNorm 0 core)

namespace StartupUniformOriginalCell

/-- Composition retains a single high budget. The intermediate full norm
is paid by the checked original rank profile, and its base norm by the
rank-independent low operator bound. -/
theorem comp {State : Type*} {input middle output rank : ℕ}
    {parameters : PhaseParameters} {budget : State → ℝ}
    {outerKernel : State → StartupL2 middle →L[ℂ] StartupL2 output}
    {innerKernel : State → StartupL2 input →L[ℂ] StartupL2 middle}
    {innerRank : State → StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension middle rank)}
    (outer : StartupUniformOriginalCell parameters rank budget outerKernel)
    (inner : StartupUniformOriginalCell parameters rank budget innerKernel)
    (innerControlled : StartupUniformOriginalRank parameters budget innerKernel innerRank)
    (budgetNonnegative : ∀ state,0≤budget state) :
    StartupUniformOriginalCell parameters rank budget (fun state => (outerKernel state).comp (innerKernel state)) := by
  obtain ⟨outerLeading,outerNonnegative,outerBound⟩ := outer
  obtain ⟨innerLeading,innerNonnegative,innerBound⟩ := inner
  obtain ⟨profile,controls⟩ := innerControlled
  refine ⟨outerLeading*innerLeading,mul_nonneg outerNonnegative innerNonnegative,?_⟩
  intro epsilon positive
  let delta := epsilon/(2*(profile.high+1))
  let eta := epsilon/(2*(outerLeading+1))
  have deltaPositive : 0<delta := div_pos positive (by linarith [profile.highNonnegative])
  have etaPositive : 0<eta := div_pos positive (by positivity)
  obtain ⟨outerTail,outerTailNonnegative,outerEstimate⟩ := outerBound delta deltaPositive
  obtain ⟨innerTail,innerTailNonnegative,innerEstimate⟩ := innerBound eta etaPositive
  refine ⟨outerLeading*innerTail+delta*profile.high+outerTail*profile.base,
    add_nonneg (add_nonneg (mul_nonneg outerNonnegative innerTailNonnegative)
      (mul_nonneg deltaPositive.le profile.highNonnegative))
      (mul_nonneg outerTailNonnegative profile.baseNonnegative),?_⟩
  intro state core image same
  let actual := (controls state).some
  have sameOuter : originalSourceFieldLinear parameters image=
      outerKernel state (originalSourceFieldLinear parameters (actual.action core)) := by
    rw [actual.same]
    exact same
  have outerApplied := outerEstimate state (actual.action core) image sameOuter
  have innerApplied := innerEstimate state core (actual.action core) (actual.same core)
  have first := mul_le_mul_of_nonneg_left innerApplied outerNonnegative
  have second := mul_le_mul_of_nonneg_left (actual.highBound core) deltaPositive.le
  have thirdBudget := mul_le_mul_of_nonneg_left (actual.baseBound core)
    (mul_nonneg outerTailNonnegative (budgetNonnegative state))
  have paid := outerApplied.trans (add_le_add (add_le_add first second) (by
    simpa only [mul_assoc,mul_left_comm,mul_comm] using thirdBudget))
  have deltaAllocated : delta*profile.high≤epsilon/2 := by
    have exactDelta : delta*(2*(profile.high+1))=epsilon := div_mul_cancel₀ epsilon (by linarith [profile.highNonnegative])
    nlinarith [deltaPositive]
  have etaAllocated : outerLeading*eta≤epsilon/2 := by
    have exactEta : eta*(2*(outerLeading+1))=epsilon := div_mul_cancel₀ epsilon (by positivity)
    nlinarith [etaPositive]
  have combined := mul_le_mul_of_nonneg_right (add_le_add etaAllocated deltaAllocated) (originalGradeNorm_nonnegative rank core)
  nlinarith only [paid,combined]

end StartupUniformOriginalCell
end Grad.CartesianStartup
