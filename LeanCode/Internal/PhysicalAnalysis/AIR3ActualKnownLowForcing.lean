import AIR2OriginalKnownSourcePacket

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularKnownLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.BoundaryKernelAction

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters L compact)

/-- Literal BF8 known low source, before the actual inverse is applied.
The g contribution is +R g after the negative output derivative acts on -r g. -/
def knownLowForcing (known : HighKnownSourceBulk lower) (g : DivisionRow 1 lower) : LowEnergyBulk lower :=
  lowFirstOutput parameters lower L
    (lowPhysicalRowAction parameters L compact lower positive bounded state 0 (knownLowSevenPacket lower known) + highSourceF lower known) +
  lowCellOutput lower L positive
    (lowPhysicalRowAction parameters L compact lower positive bounded state 1 (knownLowSevenPacket lower known)) +
  lowAngularOutput lower L positive
    (lowPhysicalRowAction parameters L compact lower positive bounded state 2 (knownLowSevenPacket lower known) - radialRadiusRow lower positive g)

/-- Continuous source map on its independent weighted bulk coordinates. -/
def knownLowForcingMap : (HighKnownSourceBulk lower × DivisionRow 1 lower) →L[ℂ] LowEnergyBulk lower :=
  (lowFirstOutput parameters lower L).comp
    (((lowPhysicalRowAction parameters L compact lower positive bounded state 0).comp (knownLowSevenPacket lower) + highSourceF lower).comp (ContinuousLinearMap.fst ℂ _ _)) +
  (lowCellOutput lower L positive).comp
    (((lowPhysicalRowAction parameters L compact lower positive bounded state 1).comp (knownLowSevenPacket lower)).comp (ContinuousLinearMap.fst ℂ _ _)) +
  (lowAngularOutput lower L positive).comp
    (((lowPhysicalRowAction parameters L compact lower positive bounded state 2).comp (knownLowSevenPacket lower)).comp (ContinuousLinearMap.fst ℂ _ _) -
      (radialRadiusRow lower positive).comp (ContinuousLinearMap.snd ℂ _ _))

theorem knownLowForcingMap_apply (known : HighKnownSourceBulk lower) (g : DivisionRow 1 lower) :
    knownLowForcingMap parameters L compact lower positive bounded state (known,g) =
      knownLowForcing parameters L compact lower positive bounded state known g := rfl

omit lower positive bounded state in
def knownLowSourceConstant : ℝ :=
  3 * ((lowBalanceConstant L parameters.gamma + 2) * knownLowRowConstant parameters L compact 0 +
    knownLowRowConstant parameters L compact 1 + 2 * knownLowRowConstant parameters L compact 2)

omit lower positive bounded state in
theorem knownLowSourceConstant_nonnegative : 0 ≤ knownLowSourceConstant parameters L compact := by
  have first := knownLowRowConstant_nonnegative parameters L compact 0
  have second := knownLowRowConstant_nonnegative parameters L compact 1
  have third := knownLowRowConstant_nonnegative parameters L compact 2
  have balance : 0 ≤ lowBalanceConstant L parameters.gamma + 2 := by
    have : 1 ≤ lowBalanceConstant L parameters.gamma := le_max_left _ _
    linarith
  unfold knownLowSourceConstant
  positivity

/-- Uniform original normalized known source estimate. -/
theorem knownLowForcing_bound (known : HighKnownSourceBulk lower) (g : DivisionRow 1 lower) :
    ‖knownLowForcing parameters L compact lower positive bounded state known g‖ ≤
      (knownLowSourceConstant parameters L compact * state.val.val.size 0 + lowBalanceConstant L parameters.gamma + 2) * ‖known‖ + 2 * ‖g‖ := by
  let packet := knownLowSevenPacket lower known
  have packetBound : ‖packet‖ ≤ 3 * ‖known‖ := knownLowSevenPacket_bound lower known
  have balance : 0 ≤ lowBalanceConstant L parameters.gamma + 2 := by
    have : 1 ≤ lowBalanceConstant L parameters.gamma := le_max_left _ _
    linarith
  have rowBound (row : Fin 3) : ‖lowPhysicalRowAction parameters L compact lower positive bounded state row packet‖ ≤
      knownLowRowConstant parameters L compact row * state.val.val.size 0 * (3 * ‖known‖) :=
    (knownLowRow_bound parameters L compact lower positive bounded state row packet).trans
      (mul_le_mul_of_nonneg_left packetBound (mul_nonneg (knownLowRowConstant_nonnegative parameters L compact row) (state.val.val.size_nonnegative 0)))
  have first := (lowFirstOutput_bound parameters lower L
    (lowPhysicalRowAction parameters L compact lower positive bounded state 0 packet + highSourceF lower known)).trans
    (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (rowBound 0) (knownBulk_coordinate_bound lower known 3))) balance)
  have second := (lowCellOutput_bound lower L positive _).trans (rowBound 1)
  have third := (lowAngularOutput_bound lower L positive
    (lowPhysicalRowAction parameters L compact lower positive bounded state 2 packet - radialRadiusRow lower positive g)).trans
    (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add (rowBound 2) (radialRadiusRow_bound lower positive g))) (by norm_num : (0 : ℝ) ≤ 2))
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  unfold knownLowSourceConstant
  linarith

end Grad.AnnularKnownLow
