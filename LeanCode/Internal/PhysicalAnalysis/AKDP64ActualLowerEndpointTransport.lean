import AKDP58ActualLedgerPrincipalEndpoint
import AKDP60SameActualPhaseGraphBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.NonlinearProduct
open Grad.OriginalCartesianTameEstimate Grad.OriginalCoreRealization
namespace StartupUniformOriginalEndpoint

/-- Transport a lower-order image estimate through the actual complete
current/principal action. Its adjustable full-norm term is preserved and
its pure-cell remainder uses only one high budget on the input base. -/
theorem absorbLower {State : Type*} {input output rank : ℕ} {parameters : PhaseParameters} {budget : State → ℝ}
    {kernel : State → StartupL2 input →L[ℂ] StartupL2 output}
    {ranked : State → StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension output rank)}
    (actual : StartupUniformOriginalEndpoint parameters budget kernel ranked)
    (budgetNonnegative : ∀ state,0≤budget state) (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ delta : ℝ,0<delta ∧ ∀ remainder : ℝ,0≤remainder → ∃ constant : ℝ,0≤constant ∧
      ∀ (state : State) (core : ACore parameters input) (image : ACore parameters output) (value : ℝ),
      originalSourceFieldLinear parameters image=kernel state (originalSourceFieldLinear parameters core) →
      value≤delta*originalGradeNorm rank image+remainder*originalCellNorm parameters rank image →
      value≤epsilon*originalGradeNorm rank core+
        constant*(originalCellNorm parameters rank core+budget state*originalGradeNorm 0 core) := by
  obtain ⟨profile,controls⟩ := actual.1
  obtain ⟨leading,leadingNonnegative,cellBound⟩ := actual.2
  let delta := epsilon/(2*(profile.high+1))
  have deltaPositive : 0<delta := div_pos positive (by linarith [profile.highNonnegative])
  refine ⟨delta,deltaPositive,?_⟩
  intro remainder remainderNonnegative
  let eta := epsilon/(2*(remainder+1))
  have etaPositive : 0<eta := div_pos positive (by positivity)
  obtain ⟨tail,tailNonnegative,cellEstimate⟩ := cellBound eta etaPositive
  refine ⟨remainder*leading+delta*profile.high+remainder*tail,
    add_nonneg (add_nonneg (mul_nonneg remainderNonnegative leadingNonnegative)
      (mul_nonneg deltaPositive.le profile.highNonnegative)) (mul_nonneg remainderNonnegative tailNonnegative),?_⟩
  intro state core image value same bounded
  let control := (controls state).some
  have identical : image=control.action core := originalSourceFieldLinear_injective parameters (same.trans (control.same core).symm)
  have imageBound : originalGradeNorm rank image≤profile.high*(originalGradeNorm rank core+budget state*originalGradeNorm 0 core) := by
    rw [identical]
    exact control.highBound core
  have first := mul_le_mul_of_nonneg_left imageBound deltaPositive.le
  have second := mul_le_mul_of_nonneg_left (cellEstimate state core image same) remainderNonnegative
  have paid := bounded.trans (add_le_add first second)
  have deltaAllocated : delta*profile.high≤epsilon/2 := by
    have exactDelta : delta*(2*(profile.high+1))=epsilon := div_mul_cancel₀ epsilon (by linarith [profile.highNonnegative])
    nlinarith [deltaPositive]
  have etaAllocated : remainder*eta≤epsilon/2 := by
    have exactEta : eta*(2*(remainder+1))=epsilon := div_mul_cancel₀ epsilon (by positivity)
    nlinarith [etaPositive]
  have main := mul_le_mul_of_nonneg_right (add_le_add deltaAllocated etaAllocated) (originalGradeNorm_nonnegative rank core)
  have cellExtra := mul_nonneg (add_nonneg (mul_nonneg deltaPositive.le profile.highNonnegative)
    (mul_nonneg remainderNonnegative tailNonnegative)) (Real.sqrt_nonneg
      (∑' cell : ℤ,(cellFrequency cell^rank*‖Grad.GaugeCoefficients.Physical.RadialLedger.apMassRow
        (cellFrequency cell) 0 (phaseWeightedJet parameters cell (core.val cell))‖)^2))
  have baseExtra := mul_nonneg (mul_nonneg remainderNonnegative leadingNonnegative)
    (mul_nonneg (budgetNonnegative state) (originalGradeNorm_nonnegative 0 core))
  change 0≤(delta*profile.high+remainder*tail)*originalCellNorm parameters rank core at cellExtra
  nlinarith only [paid,main,cellExtra,baseExtra]

end StartupUniformOriginalEndpoint
end Grad.CartesianStartup
