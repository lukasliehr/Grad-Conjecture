import AKAQ8OriginalTaylorRemainder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped BigOperators ContDiff RealInnerProductSpace
namespace Grad.OriginalFlatAxisDecay
open Grad.FourierGrade Grad.CartesianState Grad.ClosedJets Grad.COR12Extension
open Grad.COR13Completion Grad.SourceCollarDivision Grad.Constraints
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.BoundaryLift

/-- The original completed first jet vanishes, using the accepted BL32
trace and SCD22 value, with no additional decay or EX membership hypothesis. -/
def OriginalFirstJetFlat {dimension : ℕ} (parameters : PhaseParameters)
    (field : AGrade parameters dimension 4) : Prop :=
  OriginalValueFlat parameters (by omega : 3 ≤ 4) field ∧
    ∀ (cell : ℤ) (direction : Fin 2),
      completedCellDerivative parameters 1 (fun _ => direction) cell field (ambientClosedDisk 0) = 0

theorem weightedValueAt_flat {dimension : ℕ} (parameters : PhaseParameters)
    (field : AGrade parameters dimension 4) (flat : OriginalFirstJetFlat parameters field) (cell : ℤ) :
    weightedValueAt parameters cell (ambientClosedDisk 0) field = 0 :=
  originalValueFlat_weighted parameters (by omega) field flat.1 cell

theorem weightedDerivativeAt_flat {dimension : ℕ} (parameters : PhaseParameters)
    (field : AGrade parameters dimension 4) (flat : OriginalFirstJetFlat parameters field)
    (cell : ℤ) (direction : Fin 2) :
    weightedDerivativeAt parameters cell direction (ambientClosedDisk 0) field = 0 := by
  simp only [weightedDerivativeAt,add_apply,smul_apply,weightedValueAt_flat parameters field flat,
    ContinuousLinearMap.comp_apply,ContinuousMap.evalCLM_apply,flat.2,smul_zero,add_zero]

theorem weightedTaylorAt_flat {dimension : ℕ} (parameters : PhaseParameters)
    (field : AGrade parameters dimension 4) (flat : OriginalFirstJetFlat parameters field)
    (cell : ℤ) (point : ClosedDisk) :
    weightedTaylorAt parameters cell point field = completedWeightedCell parameters (by omega) cell field point := by
  simp only [weightedTaylorAt,sub_apply,smul_apply,weightedValueAt_flat parameters field flat,
    weightedDerivativeAt_flat parameters field flat,smul_zero,sub_zero]
  rfl

def originalRotationAt {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ) (point : ClosedDisk) :
    AGrade parameters dimension 4 →L[ℂ] ComplexEuclidean dimension :=
  (point.val 0 : ℂ) • ((ContinuousMap.evalCLM ℂ point).comp (completedCellDerivative parameters 1 (fun _ => 1) cell)) -
    (point.val 1 : ℂ) • ((ContinuousMap.evalCLM ℂ point).comp (completedCellDerivative parameters 1 (fun _ => 0) cell))

theorem originalRotationAt_core {dimension : ℕ} (parameters : PhaseParameters)
    (cell : ℤ) (point : ClosedDisk) (field : GradeCore parameters dimension 4) :
    originalRotationAt parameters cell point (aGradeEta parameters field) =
      (rotationJet (field.toCore.val cell)).value point := by
  simp only [originalRotationAt,sub_apply,smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousMap.evalCLM_apply,completedCellDerivative_eta]
  simp only [rotationJet,sub_eq_add_neg,closedJet_value_add,closedJet_value_neg,ContinuousMap.add_apply,
    ContinuousMap.neg_apply,coordinateJet_value,partialJet_value,partialCoefficient]
  rw [Complex.coe_smul,Complex.coe_smul]

theorem spatialBasis_inner (point : SpatialPlane) (direction : Fin 2) :
    inner ℝ point (spatialBasis direction) = point direction := by
  fin_cases direction <;> simp [spatialBasis,PiLp.inner_apply]

theorem originalPhase_rotation_zero (parameters : PhaseParameters) (cell : ℤ) (point : SpatialPlane) :
    point 0 * spatialPartial 1 (cartesianPhase parameters cell) point -
      point 1 * spatialPartial 0 (cartesianPhase parameters cell) point = 0 := by
  unfold spatialPartial
  change point 0 * fderiv ℝ (Grad.AnalyticWeights.Calculus.physicalPhase parameters.sigma0 parameters.gamma 1 cell) point (spatialBasis 1) -
    point 1 * fderiv ℝ (Grad.AnalyticWeights.Calculus.physicalPhase parameters.sigma0 parameters.gamma 1 cell) point (spatialBasis 0) = 0
  rw [Grad.AnalyticWeights.Calculus.physicalPhase_fderiv_apply,Grad.AnalyticWeights.Calculus.physicalPhase_fderiv_apply,spatialBasis_inner,spatialBasis_inner]
  ring

theorem weightedRotationRemainderAt_flat {dimension : ℕ} (parameters : PhaseParameters)
    (field : AGrade parameters dimension 4) (flat : OriginalFirstJetFlat parameters field)
    (cell : ℤ) (point : ClosedDisk) :
    weightedRotationRemainderAt parameters cell point field =
      cartesianWeight parameters cell point.val • originalRotationAt parameters cell point field := by
  simp only [weightedRotationRemainderAt,sub_apply,smul_apply,weightedDerivativeAt_flat parameters field flat,sub_zero]
  have cancelled : (point.val 0 : ℂ) * (spatialPartial 1 (cartesianPhase parameters cell) point.val : ℝ) -
      (point.val 1 : ℂ) * (spatialPartial 0 (cartesianPhase parameters cell) point.val : ℝ) = 0 := by
    have law := congrArg Complex.ofReal (originalPhase_rotation_zero parameters cell point.val)
    simpa only [Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_zero] using law
  simp only [weightedDerivativeAt,add_apply,smul_apply,originalRotationAt,sub_apply,ContinuousLinearMap.comp_apply,
    ContinuousMap.evalCLM_apply,smul_add,smul_smul]
  rw [← Complex.coe_smul]
  simp only [smul_sub,smul_smul]
  rw [sub_eq_zero.mp cancelled]
  module

end Grad.OriginalFlatAxisDecay
