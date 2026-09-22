import AKBV1OriginalMixedCoordinateNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 950000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.CartesianCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap
open Grad.WeightedJets Grad.Constraints

variable {dimension : ℕ} (parameters : PhaseParameters)
  (function : Spatial → CellValues dimension) (smooth : ContDiff ℝ ∞ function) (cells : Finset ℤ)

def finiteSmoothCellJet (cell : ℤ) : ClosedJet dimension :=
  globalClosedJet (fun point => function point cell)
    (((lp.evalCLM ℂ (fun _ : ℤ => PhysicalValue dimension) 2 cell).restrictScalars ℝ).contDiff.comp smooth)

theorem finiteSmoothCellJet_derivative {order : ℕ} (cell : ℤ)
    (word : CartesianWord order) (point : ClosedDisk) :
    closedDerivative (finiteSmoothCellJet function smooth cell) order word point =
      (Grad.Mollifier.Pointwise.orderedDerivative order word function point.val) cell := by
  exact (globalClosedJet_derivative (fun point => function point cell)
    (((lp.evalCLM ℂ (fun _ : ℤ => PhysicalValue dimension) 2 cell).restrictScalars ℝ).contDiff.comp smooth)
    word point).trans (Grad.SmoothDensity.orderedDerivative_map
      (lp.evalCLM ℂ (fun _ : ℤ => PhysicalValue dimension) 2 cell)
      order word function smooth point.val)

/-- The actual finite smooth approximation, with the original phase removed coefficientwise. -/
def finiteWeightedOriginalCore : ACore parameters dimension := by
  classical
  refine ⟨fun cell => if cell ∈ cells then phaseInverseWeightedJet parameters cell
    (finiteSmoothCellJet function smooth cell) else 0, ?_⟩
  intro grade
  rw [memlp_iff_summable_sq]
  apply summable_of_ne_finset_zero (s := cells)
  intro cell outside
  simp only [rawCartesianGradeCoordinates,if_neg outside,map_zero,norm_zero,zero_pow (by decide : 2 ≠ 0)]

theorem finiteWeightedOriginalCore_weightedJet
    (supported : ∀ point cell, cell ∉ cells → function point cell = 0) (cell : ℤ) :
    phaseWeightedJet parameters cell ((finiteWeightedOriginalCore parameters function smooth cells).val cell) =
      finiteSmoothCellJet function smooth cell := by
  classical
  by_cases member : cell ∈ cells
  · change phaseWeightedJet parameters cell (if cell ∈ cells then _ else _) = _
    rw [if_pos member,phaseWeightedJet_inverse_left]
  · change phaseWeightedJet parameters cell (if cell ∈ cells then _ else _) = _
    rw [if_neg member]
    change (phaseWeightedJetLinear parameters cell) 0 = _
    rw [map_zero]
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    exact (supported point.val cell member).symm

theorem finiteWeightedOriginalCore_value
    (supported : ∀ point cell, cell ∉ cells → function point cell = 0) (cell : ℤ) (point : ClosedDisk) :
    cartesianWeight parameters cell point.val •
      ((finiteWeightedOriginalCore parameters function smooth cells).val cell).value point = function point.val cell := by
  exact congrArg (fun jet : ClosedJet dimension => jet.value point)
    (finiteWeightedOriginalCore_weightedJet parameters function smooth cells supported cell)

/-- Each original mixed coordinate is the literal corresponding full-cell weak-jet projection. -/
theorem finiteWeightedOriginalCore_coordinates {grade : ℕ}
    (supported : ∀ point cell, cell ∉ cells → function point cell = 0)
    (jet : Mixed dimension grade openUnitDisk)
    (realized : Grad.SmoothDensity.Realizes dimension openUnitDisk (.mixed grade) function jet)
    (cell : ℤ) (index : GradeMultiIndex grade) :
    cartesianGradeCoordinates parameters grade (finiteWeightedOriginalCore parameters function smooth cells) cell index =
      fieldCellProjection dimension openUnitDisk cell (jet.val (originalJetIndexEquiv grade index)) := by
  rw [cartesianGradeCoordinates_apply,finiteWeightedOriginalCore_weightedJet parameters function smooth cells supported cell]
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul ((cellFrequency cell : ℂ)^(grade-cartesianOrder index.toCartesian))
      (closedContinuousToDiskL2 (closedMultiDerivative (finiteSmoothCellJet function smooth cell) index.toCartesian)),
    closedContinuousToDiskL2_ae (closedMultiDerivative (finiteSmoothCellJet function smooth cell) index.toCartesian),
    fieldCellProjection_ae dimension openUnitDisk (jet.val (originalJetIndexEquiv grade index)),
    realized.2,ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point scaled closed projection same inside
  rw [scaled,Pi.smul_apply,closed,closedDiskLift,dif_pos (openDiskMembershipClosed point inside),projection cell,
    same (originalJetIndexEquiv grade index) cell]
  change ((cellFrequency cell : ℂ)^(grade-cartesianOrder index.toCartesian)) •
      (closedDerivative (globalClosedJet (fun point => function point cell) _)
        (cartesianOrder index.toCartesian) (cartesianMultiIndexWord index.toCartesian) _) =
    ((cellFrequency cell : ℂ)^(grade-cartesianOrder index.toCartesian)) •
      (Grad.Mollifier.Pointwise.orderedDerivative (cartesianOrder index.toCartesian)
        (cartesianMultiIndexWord index.toCartesian) function point) cell
  congr 1
  exact finiteSmoothCellJet_derivative function smooth cell
    (cartesianMultiIndexWord index.toCartesian) ⟨point,openDiskMembershipClosed point inside⟩


/-- The original completed grade-zero cell agrees with the SAME weak-jet base. -/
theorem finiteWeightedOriginalCore_zeroCell {grade : ℕ}
    (supported : ∀ point cell, cell ∉ cells → function point cell = 0)
    (jet : Mixed dimension grade openUnitDisk)
    (realized : Grad.SmoothDensity.Realizes dimension openUnitDisk (.mixed grade) function jet)
    (cell : ℤ) :
    Grad.RawSourceFaithfulness.zeroCell parameters cell
      (aGradeEta parameters (GradeCore.ofCoreLinear
        (finiteWeightedOriginalCore parameters function smooth cells))) =
      fieldCellProjection dimension openUnitDisk cell
        (base dimension grade openUnitDisk (fun index => grade-degree index) jet) := by
  rw [Grad.RawSourceFaithfulness.zeroCell_core,
    finiteWeightedOriginalCore_weightedJet parameters function smooth cells supported cell]
  apply Lp.ext
  filter_upwards [closedContinuousToDiskL2_ae (finiteSmoothCellJet function smooth cell).value,
    fieldCellProjection_ae dimension openUnitDisk (base dimension grade openUnitDisk (fun index => grade-degree index) jet),
    realized.1,ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point closed projection same inside
  rw [closed,closedDiskLift,dif_pos (openDiskMembershipClosed point inside),projection cell]
  exact (congrArg (fun value : CellValues dimension => value cell) same).symm

end Grad.CartesianCoreRecovery
