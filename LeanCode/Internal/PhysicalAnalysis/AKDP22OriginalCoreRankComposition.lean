import AKDP21OriginalCoreRankEstimate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
namespace Grad.CartesianStartup
open Grad.NonlinearProduct Grad.Constraints.Gauges
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers
open Grad.OriginalCoreRealization Grad.NonlinearQuotientBounds

namespace StartupCoreRankProfile

def composition (outer inner : StartupCoreRankProfile) (outerBound : ℝ) (nonnegative : 0≤outerBound) : StartupCoreRankProfile where
  base := outer.base*inner.base
  high := outer.high*(inner.high+inner.base)
  remainder epsilon :=
    (epsilon/(2*(inner.high+1)))*inner.high+
      outer.remainder (epsilon/(2*(inner.high+1)))*inner.base+
        outerBound*inner.remainder (epsilon/(2*(outerBound+1)))
  baseNonnegative := mul_nonneg outer.baseNonnegative inner.baseNonnegative
  highNonnegative := mul_nonneg outer.highNonnegative (add_nonneg inner.highNonnegative inner.baseNonnegative)
  remainderNonnegative epsilon positive := by
    have delta : 0<epsilon/(2*(inner.high+1)) := div_pos positive (by linarith [inner.highNonnegative])
    have eta : 0<epsilon/(2*(outerBound+1)) := div_pos positive (by linarith)
    exact add_nonneg (add_nonneg (mul_nonneg delta.le inner.highNonnegative)
      (mul_nonneg (outer.remainderNonnegative _ delta) inner.baseNonnegative))
      (mul_nonneg nonnegative (inner.remainderNonnegative _ eta))

end StartupCoreRankProfile
namespace StartupCoreRankControl
variable {input middle output rank : ℕ} {parameters : PhaseParameters} {budget : ℝ}

/-- Composition allocates the adjustable top term before the state and
combines the lower payment into one high budget times the original M0. -/
def comp {outerProfile innerProfile : StartupCoreRankProfile}
    {outerKernel : StartupL2 middle →L[ℂ] StartupL2 output}
    {innerKernel : StartupL2 input →L[ℂ] StartupL2 middle}
    {outerRank : StartupL2 (startupTensorDimension middle rank) →L[ℂ] StartupL2 (startupTensorDimension output rank)}
    {innerRank : StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension middle rank)}
    (outer : StartupCoreRankControl parameters budget outerProfile outerKernel outerRank)
    (inner : StartupCoreRankControl parameters budget innerProfile innerKernel innerRank)
    (outerBound : ℝ) (nonnegative : 0≤outerBound) (normBound : ‖outerRank‖≤outerBound)
    (budgetNonnegative : 0≤budget) :
    StartupCoreRankControl parameters budget (outerProfile.composition innerProfile outerBound nonnegative)
      (outerKernel.comp innerKernel) (outerRank.comp innerRank) where
  action core := outer.action (inner.action core)
  same core := by rw [outer.same,inner.same]; rfl
  baseBound core := (outer.baseBound _).trans ((mul_le_mul_of_nonneg_left (inner.baseBound core)
    outerProfile.baseNonnegative).trans_eq (mul_assoc _ _ _).symm)
  highBound core := by
    have step := (outer.highBound _).trans (mul_le_mul_of_nonneg_left
      (add_le_add (inner.highBound core) (mul_le_mul_of_nonneg_left (inner.baseBound core) budgetNonnegative))
      outerProfile.highNonnegative)
    apply step.trans
    change _ ≤ outerProfile.high*(innerProfile.high+innerProfile.base)*_
    have extra := mul_nonneg (mul_nonneg outerProfile.highNonnegative innerProfile.baseNonnegative)
      (originalGradeNorm_nonnegative rank core)
    nlinarith only [extra]
  remainderBound epsilon positive core := by
    let delta := epsilon/(2*(innerProfile.high+1))
    let eta := epsilon/(2*(outerBound+1))
    have deltaPositive : 0<delta := div_pos positive (by linarith [innerProfile.highNonnegative])
    have etaPositive : 0<eta := div_pos positive (by linarith)
    have deltaBound : delta*innerProfile.high≤epsilon/2 := by
      have denom : 0<2*(innerProfile.high+1) := by linarith [innerProfile.highNonnegative]
      have exactDelta : delta*(2*(innerProfile.high+1))=epsilon := div_mul_cancel₀ _ (ne_of_gt denom)
      nlinarith only [exactDelta,deltaPositive]
    have etaBound : outerBound*eta≤epsilon/2 := by
      have denom : 0<2*(outerBound+1) := by linarith
      have exactEta : eta*(2*(outerBound+1))=epsilon := div_mul_cancel₀ _ (ne_of_gt denom)
      nlinarith only [exactEta,etaPositive]
    have outerStep := (outer.remainderBound delta deltaPositive (inner.action core)).trans
      (add_le_add (mul_le_mul_of_nonneg_left (inner.highBound core) deltaPositive.le)
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (inner.baseBound core) budgetNonnegative)
          (outerProfile.remainderNonnegative _ deltaPositive)))
    have innerStep := (outerRank.le_opNorm (startupOriginalRankLinear parameters rank (inner.action core)-
        innerRank (startupOriginalRankLinear parameters rank core))).trans
      ((mul_le_mul_of_nonneg_right normBound (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (inner.remainderBound eta etaPositive core) nonnegative))
    have split : startupOriginalRankLinear parameters rank (outer.action (inner.action core))-
        outerRank (innerRank (startupOriginalRankLinear parameters rank core)) =
      (startupOriginalRankLinear parameters rank (outer.action (inner.action core))-
        outerRank (startupOriginalRankLinear parameters rank (inner.action core)))+
      outerRank (startupOriginalRankLinear parameters rank (inner.action core)-
        innerRank (startupOriginalRankLinear parameters rank core)) := by
      rw [map_sub]
      exact (sub_add_sub_cancel _ _ _).symm
    change ‖startupOriginalRankLinear parameters rank (outer.action (inner.action core))-
      outerRank (innerRank (startupOriginalRankLinear parameters rank core))‖ ≤ _
    rw [split]
    apply ((norm_add_le _ _).trans (add_le_add outerStep innerStep)).trans
    change _ ≤ epsilon*originalGradeNorm rank core+
      (delta*innerProfile.high+outerProfile.remainder delta*innerProfile.base+
        outerBound*innerProfile.remainder eta)*(budget*originalGradeNorm 0 core)
    have top := mul_le_mul_of_nonneg_right (add_le_add deltaBound etaBound)
      (originalGradeNorm_nonnegative rank core)
    nlinarith only [top]

end StartupCoreRankControl
end Grad.CartesianStartup
