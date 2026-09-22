import AKBC23OriginalHomogeneousThirdIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.NonlinearRange Grad.FlatSourceProjection Grad.QuotientProjection
open Grad.FinitePhysicalJetLift Grad.AxisSplit Grad.OriginalKernelRetainedDecay
open Grad.SourceCollar Grad.SourceCollarCoefficients Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.NonlinearDivision Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem originalAxialDerivative_eq_coreValue {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (point : ClosedDisk) (angle : ℝ) :
    ordinaryDerivativeExtension (originalCoefficientCore parameters field) emptyCartesianWord 1
      (point,(angle : CellCircle))=coreValue (timeDerivativeCore parameters field) point angle := by
  rw [← (originalDerivative_hasSum parameters field emptyCartesianWord 1 angle point).tsum_eq]
  unfold coreValue
  apply tsum_congr
  intro cell
  rw [apFourierPhase_eq,timeDerivativeCore_val]
  simp only [cellDerivativeFactor,pow_one,closedDerivative_zero_order,closedJet_value_smul,
    ContinuousMap.smul_apply,smul_smul]
  congr 1
  ring

theorem originalValue_eq_coreValue {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (point : ClosedDisk) (angle : ℝ) :
    ordinaryDerivativeExtension (originalCoefficientCore parameters field) emptyCartesianWord 0
      (point,(angle : CellCircle))=coreValue field point angle := by
  rw [← (originalDerivative_hasSum parameters field emptyCartesianWord 0 angle point).tsum_eq]
  unfold coreValue
  apply tsum_congr
  intro cell
  rw [apFourierPhase_eq]
  simp only [cellDerivativeFactor,pow_zero,one_smul,closedDerivative_zero_order]

theorem originalReference_value (parameters : PhaseParameters) (point : ClosedDisk) (angle : ℝ) :
    coreValue (planarReferenceCore parameters) point angle=referenceStateValue point := by
  rw [planarReferenceCore,coreValue_valueMap,tamePlanarCoordinateField,singleton_coordinate,
    singleton_coordinate,coreValue_add,coreValue_coordinate,coreValue_coordinate]
  change tamePlanarInclusion
    (point.val 0 • coreValue (constantCore parameters (EuclideanSpace.single 0 1)) point angle+
      point.val 1 • coreValue (constantCore parameters (EuclideanSpace.single 1 1)) point angle)=_
  rw [coreValue_constant,coreValue_constant]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [tamePlanarInclusion,referenceStateValue]

theorem originalReference_time (parameters : PhaseParameters) :
    timeDerivativeCore parameters (planarReferenceCore parameters)=0 := by
  apply coreValue_ext
  intro point angle
  have derivative := originalCoreAxial_hasDerivAt parameters (planarReferenceCore parameters) point angle
  have same : (fun time => coreValue (planarReferenceCore parameters) point time)=
      fun _ : ℝ => referenceStateValue point := funext (originalReference_value parameters point)
  rw [same] at derivative
  have zero := derivative.unique (hasDerivAt_const angle (referenceStateValue point))
  have valueZero : coreValue (0 : ACore parameters 3) point angle=0 := by
    unfold coreValue
    have cells (cell : ℤ) : ((0 : ACore parameters 3).val cell).value point=0 := rfl
    simp only [cells,smul_zero,tsum_zero]
  exact zero.trans valueZero.symm

theorem originalPhysicalRotation_value (value : ComplexEuclidean 3) :
    physicalRotation value=tangentGeneratorMap value := by
  rw [tangentGeneratorMap_value]
  rfl

/-- The original third frame column is precisely V/L for the same total
physical state, including the original curvature and toroidal constant. -/
theorem originalFrame_axialColumn (parameters : PhaseParameters) (length epsilon : ℝ)
    (nonzero : length≠0) (base : ACore parameters 3) (point : ClosedDisk) (angle : ℝ) (row : Fin 3) :
    originalPhysicalFrameMatrix parameters length epsilon base angle point row 2=
      ((length : ℂ)⁻¹ • coreValue
        (affineStateCore parameters length ((epsilon : ℂ),planarReferenceCore parameters+base,0)) point angle) row := by
  have axial := originalAxialDerivative_eq_coreValue parameters base point angle
  have value := originalValue_eq_coreValue parameters base point angle
  unfold originalPhysicalFrameMatrix originalPhysicalFrameDeviation
  dsimp only
  rw [operatorMatrix_add,referenceFrame_matrix,axial,value]
  change _=((length : ℂ)⁻¹ • coreValue
    (timeDerivativeCore parameters (planarReferenceCore parameters+base)+
      (epsilon : ℂ) • valueMapCore parameters tangentGeneratorMap (planarReferenceCore parameters+base)+
      (length : ℂ) • eTConstantCore parameters) point angle) row
  rw [(timeDerivativeCore parameters).map_add,originalReference_time,zero_add]
  simp only [coreValue_add,coreValue_smul,coreValue_valueMap,originalReference_value,
    originalPhysicalRotation_value,map_add]
  have inverse : (length : ℂ)⁻¹*(length : ℂ)=1 := inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr nonzero)
  fin_cases row <;>
    simp [operatorMatrix,columnEmbedding_apply,eTConstantCore,coreValue_constant,smul_add,inverse]
  all_goals ring

end Grad.OriginalKernelCovariantRecovery
