import AIA7ActualCircularOutputCoordinates
import AEJ2ActualHighBulkForms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCircularForm
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularVariational
open Grad.AnnularTiltedReference Grad.AnnularKernelL2 Grad.AnnularKernelContinuity Grad.ActualBoundaryPrimitives
open Grad.GaugeCoefficients.Physical.Ledger

/-- The existing completed circular operator has its literal diagonal entries at every power. -/
theorem circularEliminatedBulkAction_ae (parameters : PhaseParameters) (L lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (power : ℕ) (field : DivisionRow 8 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      circularEliminatedBulkAction parameters L lower positive bounded power field mode radius =
      WithLp.toLp 2 ![circularEliminatedXSymbol mode (field mode radius),
        -highAngularMultiplier mode * (field mode radius 6 + (L : ℂ)⁻¹ * field mode radius 2),
        highAngularMultiplier mode * (-field mode radius 1 -
          2 * angularInverseMultiplier mode * circularEliminatedXSymbol mode (field mode radius))] := by
  have actual := completedBulkKernel_zeroShift_ae parameters power lower
    (collarRadius lower positive bounded) (collarRadius_continuous lower positive bounded)
    (fun radius => circularEliminatedBulkKernel (radialKernelParameters parameters (collarRadius lower positive bounded radius)) L)
    (regularRadialBulk_measurable parameters lower positive bounded _
      (fixedRadialKernel_regular parameters _ (fun _ _ => sameCircularEliminatedBulkKernel _ _ L)))
    (regularRadialBulkBound parameters power _
      (fixedRadialKernel_regular parameters _ (fun _ _ => sameCircularEliminatedBulkKernel _ _ L)))
    (regularRadialBulk_moment parameters power lower positive bounded _
      (fixedRadialKernel_regular parameters _ (fun _ _ => sameCircularEliminatedBulkKernel _ _ L)))
    (fun _ => circularEliminatedBulkKernel_zeroShift _ L) field
  filter_upwards [actual] with radius exactAction
  intro mode
  have equation := exactAction mode
  change circularEliminatedBulkAction parameters L lower positive bounded power field mode radius = _ at equation
  exact equation.trans (circularEliminatedBulkKernel_entry_zero _ L _ _)

/-- Literal action on the actual homogeneous physical eight-input packet. -/
theorem circularEliminatedBulkAction_packet_ae (parameters : PhaseParameters) (L lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (power : ℕ)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (field : annularEnergySpace lower L positive) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : HighAnnularMode,
      circularEliminatedBulkAction parameters L lower positive bounded power
        (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength field) mode.val radius =
      WithLp.toLp 2 ![
        -retainedBInverseMultiplier mode.val *
          (highPhysicalDerivative parameters lower L positive lengthPositive widthHalf widthLength field mode radius 0 +
            2 * highEnergyRadius lower L positive (bEnergyDecode lower L positive field) mode radius 0),
        -highEnergyCell lower L positive (bEnergyDecode lower L positive field) mode radius 0,
        -highEnergyAngularRadius lower L positive (bEnergyDecode lower L positive field) mode radius 0 -
          2 * angularInverseMultiplier mode.val * (-retainedBInverseMultiplier mode.val *
            (highPhysicalDerivative parameters lower L positive lengthPositive widthHalf widthLength field mode radius 0 +
              2 * highEnergyRadius lower L positive (bEnergyDecode lower L positive field) mode radius 0))] := by
  filter_upwards [circularEliminatedBulkAction_ae parameters L lower positive bounded power
      (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength field),
    highEightEnergyPacket_ae parameters lower L positive lengthPositive widthHalf widthLength field]
      with radius actual inputLaw
  intro mode
  rw [actual mode.val, inputLaw mode]
  have entry := circularBulk_homogeneous_entry parameters L lengthPositive mode
    (highPhysicalDerivative parameters lower L positive lengthPositive widthHalf widthLength field mode radius 0)
    (highEnergyAngularRadius lower L positive (bEnergyDecode lower L positive field) mode radius 0)
    (highEnergyCell lower L positive (bEnergyDecode lower L positive field) mode radius 0)
    (highEnergyRadius lower L positive (bEnergyDecode lower L positive field) mode radius 0)
  rw [circularEliminatedBulkKernel_entry_zero] at entry
  exact entry

theorem highBulkSlot_low {dimension : ℕ} (lower : ℝ) (slot : Fin dimension)
    (field : AnnularBulk lower) (mode : ℤ × ℤ) (low : ¬ 3 ≤ |mode.1|) :
    highBulkSlot lower slot field mode = 0 := by
  change radialMatrixUnit lower slot 0 (highBulkIntoFull lower field mode) = 0
  rw [highBulkIntoFull_low lower field mode low, map_zero]

/-- The actual circular output has no complementary angular modes. -/
theorem circularEliminatedBulkAction_low (parameters : PhaseParameters) (L lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (power : ℕ) (field : DivisionRow 8 lower)
    (mode : ℤ × ℤ) (low : ¬ 3 ≤ |mode.1|) :
    circularEliminatedBulkAction parameters L lower positive bounded power field mode = 0 := by
  apply Lp.ext
  filter_upwards [circularEliminatedBulkAction_ae parameters L lower positive bounded power field,
    Lp.coeFn_zero (ComplexEuclidean 3) 2 (volume.restrict (Icc lower 1))] with radius actual zeroLaw
  rw [actual mode, zeroLaw]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [circularEliminatedXSymbol, highAngularMultiplier, low]

end Grad.AnnularCircularForm
