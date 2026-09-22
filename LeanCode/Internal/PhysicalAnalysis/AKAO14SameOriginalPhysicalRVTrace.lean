import AKAO13LiteralSameJAndC

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualPolarFlux
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualBoundaryPrimitives Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar
open Grad.AnnularPhysicalReconstruction Grad.PhaseAlgebra Grad.AnnularLowEnergy

/-- AH23 on the same normalized inputs: the xi and Rxi slots are restored by r. -/
theorem radialPhysicalRV_sameNormalizedTrace (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact) (r : RadialPoint) (positive : 0 < r.val)
    (angular cell : ℕ) (input : SevenSlotTrace (radialKernelParameters parameters r) angular cell) :
    fullNegativeKernelAction _ angular cell (radialNormalizedPhysicalRVKernel parameters length compact state r)
      (sevenSlotFlatten _ angular cell input) =
    (r.val : ℂ) • originalPhysicalVTrace parameters length compact state r angular cell
      (fullNegativeKernelAction _ angular cell
        (radialNormalizedCovariantKernel parameters length compact state.val.val r state.val.property)
        (sevenSlotFlatten _ angular cell input)) ((r.val : ℂ) • input 3) ((r.val : ℂ) • input 1) := by
  have nonzero : (r.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  simp only [radialNormalizedPhysicalRVKernel,radialNormalizedUnprojectedRVKernel,
    fullNegativeKernelAction_comp,fullNegativeKernelAction_sub,fullNegativeKernelAction_add,
    fullNegativeKernelAction_smul,ContinuousLinearMap.comp_apply,sevenInputSlotKernel_flatten,
    originalPhysicalVTrace,map_smul,map_add,map_sub,smul_add,smul_sub,smul_smul]
  simp only [← mul_assoc,mul_inv_cancel₀ nonzero,one_mul,inv_mul_cancel₀ nonzero]
  have axial : (r.val : ℂ) * (length : ℂ)⁻¹ * (r.val : ℂ)⁻¹ * (r.val : ℂ) = (r.val : ℂ) * (length : ℂ)⁻¹ := by
    field_simp
  rw [axial]
  simp only [one_smul,mul_one]

/-- The actual native low rV coefficients equal AH23 on the SAME full physical slice.
The original outer P and both internal mean factors remain inside their prescribed operators. -/
theorem originalRV_physicalCoefficients (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (row : DivisionRow 7 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      lowRhoPhysicalCoefficient parameters lower positive
        (lowPhysicalRowAction parameters length compact lower positive bounded.le state 2 row) radius mode =
      (radius : ℂ) • negativeTraceCoefficient
        (radialKernelParameters parameters (collarRadius lower positive bounded.le radius)) 0 0
        (originalPhysicalVTrace parameters length compact state (collarRadius lower positive bounded.le radius) 0 0
          (originalPhysicalSlice parameters lower positive bounded.le
            (fullCovariantAction parameters length compact lower positive bounded.le state.val row) radius)
          ((radius : ℂ) • bulkSevenTrace parameters (collarRadius lower positive bounded.le radius)
            ((lowStorageWeight lower positive (collarRadius lower positive bounded.le radius).val : ℂ)⁻¹ • collectRadial lower row radius) 3)
          ((radius : ℂ) • bulkSevenTrace parameters (collarRadius lower positive bounded.le radius)
            ((lowStorageWeight lower positive (collarRadius lower positive bounded.le radius).val : ℂ)⁻¹ • collectRadial lower row radius) 1)) mode := by
  filter_upwards [originalPhysicalSlice_action parameters lower positive bounded.le
      (lowPhysicalRowKernel parameters length compact state 2) (lowPhysicalRowKernel_regular parameters length compact state 2) row,
    originalPhysicalSlice_action parameters lower positive bounded.le
      (fun r => radialNormalizedCovariantKernel parameters length compact state.val.val r state.val.property)
      (radialNormalizedCovariantKernel_regular parameters length compact state.val) row,
    originalPhysicalSlice_coefficient parameters lower positive bounded.le
      (lowPhysicalRowAction parameters length compact lower positive bounded.le state 2 row),
    ae_restrict_mem measurableSet_Icc] with radius outputSame covariantSame outputCoefficient inside
  let r := collarRadius lower positive bounded.le radius
  let input := (lowStorageWeight lower positive r.val : ℂ)⁻¹ • collectRadial lower row radius
  have rPositive : 0 < r.val := positive.trans_le (collarRadius_lower lower positive bounded.le radius)
  have law := radialPhysicalRV_sameNormalizedTrace parameters length compact state r rPositive 0 0
    (bulkSevenTrace parameters r input)
  rw [bulkSevenTrace_flatten] at law
  have inputSame : bulkNegativeLift parameters r 7 input = originalPhysicalSlice parameters lower positive bounded.le row radius :=
    map_smul (bulkNegativeLift parameters r 7) _ _
  rw [inputSame,← covariantSame] at law
  change originalPhysicalSlice parameters lower positive bounded.le
    (lowPhysicalRowAction parameters length compact lower positive bounded.le state 2 row) radius =
    fullNegativeKernelAction (radialKernelParameters parameters r) 0 0
      (radialNormalizedPhysicalRVKernel parameters length compact state r)
      (originalPhysicalSlice parameters lower positive bounded.le row radius) at outputSame
  rw [← outputSame] at law
  intro mode
  have coefficient := congrArg (fun trace => negativeTraceCoefficient (radialKernelParameters parameters r) 0 0 trace mode) law
  rw [negativeTraceCoefficient_smul,outputCoefficient mode] at coefficient
  dsimp only [r,input] at coefficient
  simpa only [fullCovariantAction,collarRadius_literal lower positive bounded.le radius inside] using coefficient

end Grad.ActualPolarFlux
