import AKDR3SameAngularKernelField

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.CartesianStartup Grad.PDEBootstrap Grad.GenericCarriers
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.ActualOriginalSourceMoments
open Grad.ActualScalarWeakEquations Grad.Constraints Grad.NonlinearQuotientBounds

/-- The actual original weighted field, preserving its existing source realization. -/
def originalSourceFieldLinear {dimension : ℕ} (parameters : PhaseParameters) :
    ACore parameters dimension →ₗ[ℂ] StartupL2 dimension where
  toFun field := (originalSourceMoments parameters field).field
  map_add' first second := by
    apply startupField_ae_ext
    filter_upwards [originalSource_field_closed parameters (first+second),
      originalSource_field_closed parameters first,originalSource_field_closed parameters second,
      Lp.coeFn_add (originalSourceMoments parameters first).field (originalSourceMoments parameters second).field,
      ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point total one two added inside
    intro cell
    rw [added]
    simp only [lp.coeFn_add,Pi.add_apply]
    rw [total cell,one cell,two cell]
    simp only [closedDiskLift,dif_pos (openDiskMembershipClosed point inside),phaseWeightedJet_value]
    change cartesianWeight parameters cell point • ((first.val cell+second.val cell).value _) = _
    rw [closedJet_value_add,ContinuousMap.add_apply,smul_add]
  map_smul' scalar field := by
    apply startupField_ae_ext
    filter_upwards [originalSource_field_closed parameters (scalar • field),
      originalSource_field_closed parameters field,
      Lp.coeFn_smul scalar (originalSourceMoments parameters field).field,
      ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point total one scaled inside
    intro cell
    simp only [RingHom.id_apply]
    rw [scaled]
    simp only [lp.coeFn_smul,Pi.smul_apply]
    rw [total cell,one cell]
    simp only [closedDiskLift,dif_pos (openDiskMembershipClosed point inside),phaseWeightedJet_value]
    change cartesianWeight parameters cell point • ((scalar • field.val cell).value _) = _
    rw [closedJet_value_smul,ContinuousMap.smul_apply]
    exact smul_comm _ _ _

theorem originalSourceFieldLinear_valueMap {input output : ℕ} (parameters : PhaseParameters)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) (field : ACore parameters input) :
    originalSourceFieldLinear parameters (valueMapCore parameters mapping field) =
      originalValueKernel mapping (originalSourceFieldLinear parameters field) := by
  apply startupField_ae_ext
  filter_upwards [originalSource_field_closed parameters (valueMapCore parameters mapping field),
    originalSource_field_closed parameters field,
    startupPointKernel_field_ae mapping (LinearIsometryEquiv.refl ℝ _) (originalSourceFieldLinear parameters field),
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point outputSame inputSame mapped inside
  intro cell
  change ∀ cell, (originalValueKernel mapping (originalSourceFieldLinear parameters field)) point cell =
    mapping ((originalSourceFieldLinear parameters field) point cell) at mapped
  change (originalSourceMoments parameters (valueMapCore parameters mapping field)).field point cell = _
  rw [outputSame cell,mapped cell]
  change _ = mapping ((originalSourceMoments parameters field).field point cell)
  rw [inputSame cell]
  simp only [closedDiskLift,dif_pos (openDiskMembershipClosed point inside),phaseWeightedJet_value,
    valueMapCore_value]
  exact (mapping.map_smul_of_tower (cartesianWeight parameters cell point) _).symm

end Grad.OriginalCoreRealization
