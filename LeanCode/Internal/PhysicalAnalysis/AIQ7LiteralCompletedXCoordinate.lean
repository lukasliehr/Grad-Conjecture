import AIQ6CompletedFirstRowElimination

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularPhysicalSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularKernelContinuity
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource Grad.AnnularCurrentSolution Grad.AnnularCurrentGreen
open Grad.AnnularCircularForm Grad.ActualBoundaryInverse Grad.GaugeCoefficients.Physical.Ledger

theorem regularMatrixUnit_eq_bulk {input output : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (row : Fin output) (column : Fin input) :
    regularRadialBulkAction parameters power lower positive bounded
      (fun radius => constantMatrixKernel (radialKernelParameters parameters radius) input output (matrixUnit row column))
      (constantMatrixRadialKernel_regular parameters input output (matrixUnit row column)) = bulkMatrixUnit lower row column := by
  apply ContinuousLinearMap.ext
  intro field
  apply Subtype.ext
  funext mode
  apply Lp.ext
  have actual : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ index,
      regularRadialBulkAction parameters power lower positive bounded
        (fun r => constantMatrixKernel (radialKernelParameters parameters r) input output (matrixUnit row column))
        (constantMatrixRadialKernel_regular parameters input output (matrixUnit row column)) field index radius =
        matrixUnit row column (field index radius) := by
    unfold regularRadialBulkAction constantMatrixKernel
    apply completedBulkKernel_diagonal_ae
  filter_upwards [actual, bulkMatrixUnit_ae lower row column field] with radius literal component
  rw [literal mode, component mode, matrixUnit_apply]

theorem eliminatedBulkKernel_first (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (radius : RadialPoint) :
    fullKernelComposition (coordinateProjectionKernel (radialKernelParameters parameters radius) 3 0)
      (radialEliminatedBulkKernel parameters L compact state radius) =
      radialEliminatedXKernel parameters L compact state radius := by
  unfold radialEliminatedBulkKernel
  rw [fullKernelComposition_add_inner, fullKernelComposition_add_inner]
  simp only [← fullKernelComposition_assoc, coordinateProjection_injection_same,
    coordinateProjection_injection_distinct _ 3 0 1 (by decide),
    coordinateProjection_injection_distinct _ 3 0 2 (by decide),
    fullIdentityKernel_comp_rect, fullKernel_zero_comp, fullKernel_add_zero]

/-- The first completed physical output is exactly the SAME actual retained inverse action. -/
theorem eliminatedBulkAction_first (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) :
    (bulkMatrixUnit lower (0 : Fin 1) (0 : Fin 3)).comp
      (eliminatedBulkAction parameters L compact lower positive bounded state power) =
      eliminatedXAction parameters L compact lower positive bounded state power := by
  rw [← regularMatrixUnit_eq_bulk parameters power lower positive bounded,
    eliminatedBulkAction_eq_regular, eliminatedXAction_eq_regular, ← regularRadialBulkAction_comp]
  apply regularRadialBulkAction_congr
  exact eliminatedBulkKernel_first parameters L compact state

theorem bulkScalarProjection_distinct {dimension : ℕ} (lower : ℝ) (row column : Fin dimension)
    (different : row ≠ column) (field : DivisionRow 1 lower) :
    bulkMatrixUnit lower (0 : Fin 1) row (bulkMatrixUnit lower column 0 field) = 0 := by
  apply ext_inner_left ℂ
  intro test
  rw [← bulkPhysicalSlot_pairing, bulkScalarSlots_inner, if_neg different, inner_zero_right]

theorem directKnownThreePacket_first (lower : ℝ) (positive : 0 < lower) (source : HighAuxiliarySourceBulk lower) :
    bulkMatrixUnit lower (0 : Fin 1) (0 : Fin 3) (directKnownThreePacket lower positive source) = 0 := by
  change bulkMatrixUnit lower (0 : Fin 1) (0 : Fin 3)
    (bulkMatrixUnit lower (1 : Fin 3) (0 : Fin 1) (source 1) +
      bulkMatrixUnit lower (2 : Fin 3) (0 : Fin 1) (source 2 - radialRadiusRow lower positive (source 0))) = 0
  rw [map_add, bulkScalarProjection_distinct lower 0 1 (by decide),
    bulkScalarProjection_distinct lower 0 2 (by decide), add_zero]

/-- Including every known source, the complete physical x is precisely the actual first-row elimination. -/
theorem actualFullHighOutput_first (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (field : Grad.AnnularVariational.annularEnergySpace lower L positive)
    (known : HighKnownSourceBulk lower) (auxiliary : HighAuxiliarySourceBulk lower) :
    bulkMatrixUnit lower (0 : Fin 1) (0 : Fin 3)
      (actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field known auxiliary) =
      eliminatedXAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
        (fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength (field, known)) := by
  rw [actualFullHighOutput_one_packet, map_add, directKnownThreePacket_first, add_zero]
  exact congrArg (fun action : DivisionRow 8 lower →L[ℂ] DivisionRow 1 lower => action
    (fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength (field, known)))
    (eliminatedBulkAction_first parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0)

end Grad.AnnularPhysicalSolution
