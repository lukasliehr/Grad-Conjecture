import AEI19OriginalCommonBalancingDiagonal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.ActualBoundaryPrimitives Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Ledger

theorem lowCircularResponse_ae (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : LowEnergyBulk lower) (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowCircularResponse parameters length lower lengthPositive positive bounded field index radius =
        if index.1 = 0 then
          (-2 / radius / lowMu length radius index.2.val.2 : ℝ) • field (0, index.2) radius -
            (lowAmplitude length parameters.gamma index.2 * lowCircularB index.2) • field (1, index.2) radius
        else
          (-lowCircularPotential length radius index.2 / (lowAmplitude length parameters.gamma index.2 * lowMu length radius index.2.val.2 ^ 2) : ℝ) • field (0, index.2) radius +
            (2 / radius / lowMu length radius index.2.val.2 : ℝ) • field (1, index.2) radius := by
  let input := lowNormalizedSevenInput parameters lower length lengthPositive positive field
  let rows := fun row => lowCircularRowAction parameters length lower positive bounded row input
  let first := lowFirstOutput parameters lower length (rows 0)
  let cell := lowCellOutput lower length positive (rows 1)
  let angular := lowAngularOutput lower length positive (rows 2)
  filter_upwards [lowFirstOutput_ae parameters lower length (rows 0) index,
    lowCellOutput_ae lower length positive (rows 1) index,
    lowAngularOutput_ae lower length positive (rows 2) index,
    lowCircularRowAction_ae parameters length lower positive bounded 0 input,
    lowCircularRowAction_ae parameters length lower positive bounded 1 input,
    lowCircularRowAction_ae parameters length lower positive bounded 2 input,
    lowNormalizedSevenInput_ae parameters lower length lengthPositive positive field index.2,
    Lp.coeFn_add (first index + cell index) (angular index), Lp.coeFn_add (first index) (cell index),
    ae_restrict_mem measurableSet_Icc] with radius firstLaw cellLaw angularLaw firstRow cellRow angularRow inputLaw total partialSum inside
  change ((first index + cell index) + angular index) radius = _
  rw [total]
  simp only [Pi.add_apply]
  rw [partialSum]
  simp only [Pi.add_apply]
  change (lowFirstOutput parameters lower length (rows 0) index radius + lowCellOutput lower length positive (rows 1) index radius) +
    lowAngularOutput lower length positive (rows 2) index radius = _
  rw [firstLaw, cellLaw, angularLaw]
  have row0 := firstRow index.2.val
  have row1 := cellRow index.2.val
  have row2 := angularRow index.2.val
  change rows 0 index.2.val radius = _ at row0
  change rows 1 index.2.val radius = _ at row1
  change rows 2 index.2.val radius = _ at row2
  change input index.2.val radius = _ at inputLaw
  rw [inputLaw] at row0 row1 row2
  have firstScalar := lowCircularFirst_normalized parameters length lower positive index.2 radius inside.1
    (field (0, index.2) radius) (field (1, index.2) radius) (collarRadius lower positive bounded radius)
  have secondScalar := lowCircularSecond_normalized parameters length lower lengthPositive positive index.2 radius inside.1
    (field (0, index.2) radius) (field (1, index.2) radius) (collarRadius lower positive bounded radius)
  rcases index with ⟨row, mode⟩
  have cases : row = 0 ∨ row = 1 := by omega
  rcases cases with rfl | rfl
  · simp only [Fin.reduceEq, ite_true, ite_false, add_zero]
    rw [row0]
    apply PiLp.ext
    intro slot
    have slotZero : slot = 0 := Subsingleton.elim _ _
    subst slot
    simpa only [PiLp.smul_apply, PiLp.sub_apply, Complex.real_smul] using firstScalar
  · simp only [Fin.reduceEq, ite_true, ite_false, zero_add]
    rw [row1, row2]
    apply PiLp.ext
    intro slot
    have slotZero : slot = 0 := Subsingleton.elim _ _
    subst slot
    simpa only [PiLp.smul_apply, PiLp.add_apply, Complex.real_smul, smul_eq_mul, mul_assoc] using secondScalar

end Grad.AnnularCurrentLow
