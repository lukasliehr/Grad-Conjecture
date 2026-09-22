import AJL6ExactPolynomialPhysicalAction
import AJI12ActualFullPhysicalRowsSmooth

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal
namespace Grad.AnnularSmoothSources
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularRadialSmoothness Grad.AnnularCurrentLow
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularKernelContinuity
open Grad.AnnularReconstruction Grad.AnnularStrongOrbit Grad.AnnularStrongSolution Grad.AnnularKnownLow
open Grad.AnnularSmoothCore

/-- Applying a genuine smooth kernel family preserves a smooth Hilbert curve. -/
theorem smoothPolynomialFamily_apply {source target : ℕ}
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target)
    (smoothKernel : SmoothPolynomialFamily parameters lower positive bounded kernel)
    (power : ℕ) (curve : ℝ → CellL2 source) (smoothCurve : ContDiffOn ℝ ∞ curve (Icc lower 1)) :
    ContDiffOn ℝ ∞ (fun radius => radialPolynomialAction parameters lower positive bounded kernel power radius
      (curve radius)) (Icc lower 1) :=
  (((ContinuousLinearMap.restrictScalarsIsometry ℂ (CellL2 source) (CellL2 target) ℝ ℝ).toContinuousLinearMap.contDiff).comp_contDiffOn
    (smoothKernel power)).clm_apply smoothCurve

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact) (core : OriginalSmoothSourceCore parameters)

/-- SAME j, c and rV acting on the once-only known source packet. -/
def smoothKnownPhysicalRowCurve (row : Fin 3) (power : ℕ) (radius : ℝ) : CellL2 1 :=
  radialPolynomialAction parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state row) power radius
    (smoothKnownSourceCurve parameters lower length positive bounded.le lengthPositive core power radius)

theorem smoothKnownPhysicalRowCurve_smooth (row : Fin 3) (power : ℕ) :
    ContDiffOn ℝ ∞ (smoothKnownPhysicalRowCurve parameters length compact lower positive bounded lengthPositive state core row power)
      (Icc lower 1) :=
  smoothPolynomialFamily_apply parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state row)
    (sameFullPhysicalRows_smooth parameters length compact state lower positive bounded row)
    power (smoothKnownSourceCurve parameters lower length positive bounded.le lengthPositive core power)
    (smoothKnownSourceCurve_smooth parameters lower length positive bounded.le lengthPositive core power)

/-- Literal normalized bulk action, decoded by the original AJG9/10 weight. -/
theorem smoothKnownPhysicalRowCurve_actual (row : Fin 3) (power : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      smoothKnownPhysicalRowCurve parameters length compact lower positive bounded lengthPositive state core row power radius mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
          lowRhoPhysicalCoefficient parameters lower positive
            (lowPhysicalRowAction parameters length compact lower positive bounded.le state row
              (knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded.le
                ((strongSmoothDenseMap parameters lower length positive bounded.le lengthPositive).mapping core)))) radius mode :=
  radialPolynomialAction_actual parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state row)
    (lowPhysicalRowKernel_regular parameters length compact state row)
    (knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded.le
      ((strongSmoothDenseMap parameters lower length positive bounded.le lengthPositive).mapping core)))
    power (smoothKnownSourceCurve parameters lower length positive bounded.le lengthPositive core power)
    (smoothKnownSourceCurve_actual parameters lower length positive bounded.le lengthPositive core power)

end Grad.AnnularSmoothSources
