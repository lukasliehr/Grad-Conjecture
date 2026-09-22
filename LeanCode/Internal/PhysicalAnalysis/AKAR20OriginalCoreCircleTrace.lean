import AKAR18ActualSmoothCircleConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators ENNReal
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceCollarRestriction
open Grad.BoundaryLift Grad.PhaseAlgebra Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.NonlinearProduct Grad.AxisSplit
open Grad.NonlinearRange Grad.NonlinearQuotientBounds Grad.Constraints

variable {dimension : ℕ}
def originalCoreWeightedCircleCell (parameters : PhaseParameters) (field : ACore parameters dimension)
    (radius : RadialPoint) (cell : ℤ) (angle : ℝ) : ComplexEuclidean dimension :=
  (cellFrequency cell : ℂ) • (phaseWeightedJet parameters cell (field.val cell)).value
    (Grad.SourceCollarDivision.polarClosedPoint radius.val angle radius.property.1 radius.property.2)

theorem originalCoreWeightedCircleCell_continuous (parameters : PhaseParameters) (field : ACore parameters dimension)
    (radius : RadialPoint) (cell : ℤ) : Continuous (originalCoreWeightedCircleCell parameters field radius cell) :=
  ((phaseWeightedJet parameters cell (field.val cell)).value.continuous.comp
    ((polarPlane_smooth.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _)).const_smul (cellFrequency cell : ℂ)

theorem originalCoreWeightedCircleCell_energy (parameters : PhaseParameters) (field : ACore parameters dimension)
    (radius : RadialPoint) (cells : Finset ℤ) (angle : ℝ) :
    ∑ cell ∈ cells, ‖originalCoreWeightedCircleCell parameters field radius cell angle‖^2 ≤
      (6*diskSupConstant*originalGradeNorm 3 field)^2 := by
  let coordinates : lp (fun _ : ℤ => CartesianGradeRow dimension 3) 2 :=
    ⟨rawCartesianGradeCoordinates parameters 3 field.val,field.property 3⟩
  have each (cell : ℤ) : ‖originalCoreWeightedCircleCell parameters field radius cell angle‖ ≤
      (6*diskSupConstant)*‖coordinates cell‖ := by
    have paid := weighted_word_sup_paid (grade := 3) (power := 1) parameters cell (field.val cell) emptyCartesianWord (by omega)
    simp only [pow_one,closedDerivative_zero_order] at paid
    rw [originalCoreWeightedCircleCell,norm_smul,Complex.norm_real,Real.norm_of_nonneg (cellFrequency_pos _).le]
    exact (mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm _ _) (cellFrequency_pos cell).le).trans
      (by simpa only [coordinates,raw_norm_eq_row] using paid)
  have sum : HasSum (fun cell : ℤ => ‖coordinates cell‖^2) (‖coordinates‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) coordinates
  calc
    _ ≤ ∑ cell ∈ cells, ((6*diskSupConstant)*‖coordinates cell‖)^2 :=
      Finset.sum_le_sum (fun cell _ => pow_le_pow_left₀ (norm_nonneg _) (each cell) 2)
    _ = (6*diskSupConstant)^2 * ∑ cell ∈ cells, ‖coordinates cell‖^2 := by simp only [mul_pow,Finset.mul_sum]
    _ ≤ (6*diskSupConstant)^2 * ‖coordinates‖^2 :=
      mul_le_mul_of_nonneg_left ((sum.summable.sum_le_tsum cells (fun _ _ => sq_nonneg _)).trans_eq sum.tsum_eq) (sq_nonneg _)
    _ = _ := by
      rw [originalGradeNorm_eq_lp]
      change (6*diskSupConstant)^2*‖coordinates‖^2 = (6*diskSupConstant*‖coordinates‖)^2
      ring

/-- An auxiliary trace of any original smooth core, used only for exact
identification. Final kernel decay is paid by the original flat A4 theorem. -/
def originalCoreCircleTrace (parameters : PhaseParameters) (field : ACore parameters dimension) (radius : RadialPoint) : CellL2 dimension :=
  originalCircleFamilyVector (originalCoreWeightedCircleCell parameters field radius)
    (originalCoreWeightedCircleCell_continuous parameters field radius) (6*diskSupConstant*originalGradeNorm 3 field)
    (originalCoreWeightedCircleCell_energy parameters field radius)

theorem originalCoreCircleTrace_represents (parameters : PhaseParameters) (field : ACore parameters dimension) (radius : RadialPoint) :
    OriginalCircleRepresents parameters radius (originalCoreCircleTrace parameters field radius) (originalCoreCircle parameters field radius) := by
  intro mode
  change (lambdaCircleWeight parameters radius.val mode : ℂ)⁻¹ •
    angularCoefficient (originalCoreWeightedCircleCell parameters field radius mode.2) mode.1 = _
  have weighted : originalCoreWeightedCircleCell parameters field radius mode.2 =
      (lambdaCircleWeight parameters radius.val mode : ℂ) •
        (fun angle => (field.val mode.2).value (Grad.SourceCollarDivision.polarClosedPoint radius.val angle radius.property.1 radius.property.2)) := by
    funext angle
    unfold originalCoreWeightedCircleCell
    rw [phaseWeightedJet_value,← Complex.coe_smul]
    change (cellFrequency mode.2 : ℂ) • ((cartesianWeight parameters mode.2 (polarPlane (radius.val,angle)) : ℂ) • _) = _
    rw [cartesianWeight_polar parameters mode.2 radius.val angle radius.property.1,smul_smul]
    unfold lambdaCircleWeight
    push_cast
    rw [mul_comm]
    rfl
  rw [weighted,angularCoefficient_smul_continuous,smul_smul,inv_mul_cancel₀
    (Complex.ofReal_ne_zero.mpr (lambdaCircleWeight_positive parameters radius.val mode).ne'),one_smul]
  unfold doubleCoefficient
  simp_rw [originalCoreCircle_axialCoefficient]

/-- Exact representations in the original weighted coordinates are unique. -/
theorem OriginalCircleRepresents.unique {parameters : PhaseParameters} {radius : RadialPoint}
    {first second : CellL2 dimension} {source : ℝ × ℝ → ComplexEuclidean dimension}
    (one : OriginalCircleRepresents parameters radius first source) (two : OriginalCircleRepresents parameters radius second source) :
    first=second := by
  apply lp.ext
  funext mode
  have equal := (one mode).trans (two mode).symm
  have weighted := congrArg (fun value => (lambdaCircleWeight parameters radius.val mode : ℂ) • value) equal
  change (_ : ℂ) • ((_ : ℂ)⁻¹ • first mode) = (_ : ℂ) • ((_ : ℂ)⁻¹ • second mode) at weighted
  simpa only [smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (lambdaCircleWeight_positive parameters radius.val mode).ne')] using weighted

end Grad.OriginalKernelRetainedDecay
