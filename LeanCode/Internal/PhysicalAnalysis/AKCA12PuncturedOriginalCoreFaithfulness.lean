import AKCA11ActualRecoveredVectorFirstJets
import AKBC16OriginalGaugeStorageFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.Cor18
open Grad.NonlinearRange Grad.SourceCollar Grad.SourceCollarFullSource Grad.BoundaryTrace
open Grad.CartesianCoreRecovery Grad.ActualPuncturedFamily Grad.ActualAnnularExhaustion

 theorem coreValue_originalPhysical {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (point : ClosedDisk) (axial : ℝ) :
    coreValue field point axial = (originalPhysicalClosedJet parameters field).value (point,(axial : CellCircle)) :=
  sourceCoreValue_eq_originalPhysicalEvaluationLift field point axial

 theorem coreValue_axial_continuous {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (point : ClosedDisk) :
    Continuous (fun axial => coreValue field point axial) := by
  simp_rw [coreValue_originalPhysical]
  exact (originalPhysicalClosedJet parameters field).value.continuous.comp
    (continuous_const.prodMk (show Continuous (fun axial : ℝ => (axial : CellCircle)) from QuotientAddGroup.continuous_mk))

 theorem coreValue_angularCoefficient {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (point : ClosedDisk) (cell : ℤ) :
    angularCoefficient (fun axial => coreValue field point axial) cell = (field.val cell).value point := by
  simp_rw [coreValue_originalPhysical]
  exact originalPhysicalClosedJet_angularCell parameters field point cell

 theorem coreValue_coordinate_zero {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (point : ClosedDisk) (coordinate : Fin dimension)
    (zero : ∀ axial,coreValue field point axial coordinate=0) (cell : ℤ) :
    (field.val cell).value point coordinate=0 := by
  rw [← coreValue_angularCoefficient parameters field point cell,
    angularCoefficient_component _ (coreValue_axial_continuous parameters field point) coordinate cell]
  simp_rw [zero]
  simp [angularCoefficient_constant]

 theorem closedJet_zero_of_punctured {dimension : ℕ} (field : ClosedJet dimension)
    (zero : ∀ point : ClosedDisk,0 < ‖point.val‖ → field.value point=0) : field=0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change field.value point=0
  by_cases nonzero : point.val=0
  · have equality : point=originPoint := Subtype.ext nonzero
    rw [equality]
    change originValue field=0
    rw [← closedJetRay_zero field 0]
    have limit := (closedJetRay_continuous field 0).continuousAt.tendsto.comp
      (originalExhaustionRadius_tendsto 1)
    have zeros (index : ℕ) : closedJetRay field 0 (originalExhaustionRadius 1 index)=0 := by
      have positive := originalExhaustionRadius_positive 1 (by norm_num) index
      have bounded := (originalExhaustionRadius_half 1 (by norm_num) index).trans (by norm_num : (1:ℝ)/2 ≤ 1)
      have norm : ‖originalExhaustionRadius 1 index • spatialBasis 0‖=originalExhaustionRadius 1 index := by
        rw [norm_smul,Grad.BoundaryLift.spatialBasis_norm,mul_one,Real.norm_of_nonneg positive.le]
      let diskPoint : ClosedDisk := ⟨originalExhaustionRadius 1 index • spatialBasis 0,by change ‖_‖≤1; rwa [norm]⟩
      exact (smoothClosedExtension_value field diskPoint).trans
        (zero diskPoint (by rw [norm]; exact positive))
    have same : (fun index => closedJetRay field 0 (originalExhaustionRadius 1 index))=fun _ => 0 := funext zeros
    change Tendsto (fun index => closedJetRay field 0 (originalExhaustionRadius 1 index)) atTop (𝓝 (closedJetRay field 0 0)) at limit
    rw [same] at limit
    exact tendsto_nhds_unique limit tendsto_const_nhds
  · exact zero point (norm_pos_iff.mpr nonzero)

 theorem originalCore_zero_of_puncturedValues {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension)
    (zero : ∀ point : ClosedDisk,0 < ‖point.val‖ → ∀ axial,coreValue field point axial=0) : field=0 := by
  apply Subtype.ext
  funext cell
  apply closedJet_zero_of_punctured
  intro point nonzero
  apply PiLp.ext
  intro coordinate
  exact coreValue_coordinate_zero parameters field point coordinate
    (fun axial => congrArg (fun value : ComplexEuclidean dimension => value coordinate) (zero point nonzero axial)) cell

end Grad.OriginalCoreRealization
