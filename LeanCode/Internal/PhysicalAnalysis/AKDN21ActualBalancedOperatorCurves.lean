import AKDN20LinearEulerAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothness Grad.AnnularKernelL2

/-- The same actual phase curve is smooth to every finite order; reserves
are used only for this fidelity statement, never in its sharp norm bound. -/
theorem actualPhaseCurve_smooth {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (curve : ℕ → ℝ → CellL2 dimension)
    (smooth : ∀ power, ContDiffOn ℝ ∞ (curve power) (Icc lower 1))
    (same : ∀ power reserve radius, radius ∈ Icc lower 1 → ∀ mode,
      curve (power+reserve) radius mode=(annularFrequency mode.1 mode.2 : ℂ)^reserve • curve power radius mode)
    (grade : ℕ) :
    ContDiffOn ℝ ∞
      (fun point => balancedPhaseAction parameters dimension (collarRadius lower positive bounded.le point) (curve (grade+1) point)) (Icc lower 1) := by
  apply contDiffOn_infty.mpr
  intro order
  let reserve := order+5
  let operator := balancedReservedPhaseAction parameters dimension (reserve+1)
  have operatorSmooth : ContDiffOn ℝ order operator (Icc lower 1) :=
    balancedReservedPhaseAction_smooth parameters dimension (reserve+1) order (by omega) lower bounded
  have realSmooth := ((ContinuousLinearMap.restrictScalarsIsometry ℂ (CellL2 dimension) (CellL2 dimension) ℝ ℝ).toContinuousLinearMap.contDiff).comp_contDiffOn operatorSmooth
  have mapped := realSmooth.clm_apply (contDiffOn_infty.mp (smooth (grade+1+reserve)) order)
  apply mapped.congr
  intro point member
  have action := balancedReservedPhaseAction_sameEuler parameters dimension reserve 0 (by dsimp only [reserve]; omega)
    lower positive bounded (collarRadius lower positive bounded.le point)
    (by simpa only [collarRadius_literal lower positive bounded.le point member] using member)
    (curve (grade+1+reserve) point) (curve (grade+1) point) (same (grade+1) reserve point member)
  rw [balancedPhaseEulerAction_zero,collarRadius_literal lower positive bounded.le point member] at action
  exact action.symm

theorem balancedFluxOutput_smooth (parameters : PhaseParameters) (length : ℝ) :
    ContDiff ℝ ∞ (balancedFluxOutput parameters length) := by
  rw [show balancedFluxOutput parameters length = fun point => balancedFluxOutput parameters length 0+point • balancedFluxSlope parameters length from
    funext (balancedFluxOutput_affine parameters length)]
  exact contDiff_const.add (contDiff_id.smul contDiff_const)

theorem balancedFluxCurve_smooth (parameters : PhaseParameters) (length : ℝ) (domain : Set ℝ)
    (curve : ℝ → PhysicalHilbertTriple) (smooth : ContDiffOn ℝ ∞ curve domain) :
    ContDiffOn ℝ ∞ (fun point => balancedFluxOutput parameters length point (curve point)) domain := by
  have realSmooth := ((ContinuousLinearMap.restrictScalarsIsometry ℂ PhysicalHilbertTriple PhysicalHilbertPair ℝ ℝ).toContinuousLinearMap.contDiff).comp_contDiffOn
    ((balancedFluxOutput_smooth parameters length).contDiffOn (s := domain))
  exact realSmooth.clm_apply smooth

end Grad.OriginalCartesianTameEstimate
