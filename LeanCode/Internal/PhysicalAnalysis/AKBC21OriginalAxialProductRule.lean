import AKBC20OriginalHomogeneousFirstIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.NonlinearRange Grad.FlatSourceProjection Grad.QuotientProjection
open Grad.FinitePhysicalJetLift Grad.AxisSplit Grad.BoundaryLift Grad.BoundaryTrace
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.OriginalKernelRetainedDecay

theorem originalCoreAxial_hasDerivAt {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (point : ClosedDisk) (angle : ℝ) :
    HasDerivAt (fun time => coreValue field point time)
      (coreValue (timeDerivativeCore parameters field) point angle) angle := by
  let term (cell : ℤ) (time : ℝ) := axialPhase cell time • (field.val cell).value point
  let slope (cell : ℤ) (time : ℝ) := axialPhase cell time • ((timeDerivativeCore parameters field).val cell).value point
  have norms := Grad.Cor18.cell_sup_norm_summable (timeDerivativeCore parameters field)
  have phase (cell : ℤ) (time : ℝ) : axialPhase cell time=cellExponential cell time :=
    (axialPhase_eq_character cell time).trans (cellCharacter_coe cell time)
  have each (cell : ℤ) (time : ℝ) : HasDerivAt (term cell) (slope cell time) time := by
    have derivative : HasDerivAt (fun argument : ℝ => cellExponential cell argument • (field.val cell).value point)
        ((Complex.I*(cell : ℂ)*cellExponential cell time) • (field.val cell).value point) time :=
      (Grad.AnnularOrbitGenerators.cellExponential_hasDerivAt cell time).smul_const ((field.val cell).value point)
    convert derivative using 1
    · funext argument
      exact congrArg (fun scalar : ℂ => scalar • (field.val cell).value point) (phase cell argument)
    · change axialPhase cell time • (((cell : ℂ)*Complex.I) • (field.val cell).value point)=_
      rw [phase,smul_smul]
      congr 1
      ring
  have bound (cell : ℤ) (time : ℝ) : ‖slope cell time‖≤‖((timeDerivativeCore parameters field).val cell).value‖ := by
    dsimp only [slope]
    rw [norm_smul,norm_axialPhase,one_mul]
    exact ContinuousMap.norm_coe_le_norm _ _
  exact hasDerivAt_tsum norms each bound (coreValue_summable field point 0) angle

/-- Axial differentiation is the genuine full-cell Fourier derivative and
obeys the literal bilinear Leibniz rule on the original all-grade core. -/
theorem originalDot_time {parameters : PhaseParameters} (first second : ACore parameters 3) :
    timeDerivativeCore parameters (dotOperation parameters first second)=
      dotOperation parameters (timeDerivativeCore parameters first) second+
        dotOperation parameters first (timeDerivativeCore parameters second) := by
  apply coreValue_ext
  intro point axial
  let product := physicalBilinear physicalDotProduct
  let realProduct := (ContinuousLinearMap.restrictScalarsL ℂ (ComplexEuclidean 3) (ComplexEuclidean 1) ℝ ℝ).comp (product.restrictScalars ℝ)
  have mapped := (realProduct.hasFDerivAt).comp_hasDerivAt axial (originalCoreAxial_hasDerivAt parameters first point axial)
  have derivative := mapped.clm_apply (originalCoreAxial_hasDerivAt parameters second point axial)
  change HasDerivAt (fun time => product (coreValue first point time) (coreValue second point time))
    (product (coreValue (timeDerivativeCore parameters first) point axial) (coreValue second point axial)+
      product (coreValue first point axial) (coreValue (timeDerivativeCore parameters second) point axial)) axial at derivative
  have original := originalCoreAxial_hasDerivAt parameters (dotOperation parameters first second) point axial
  have same : (fun time => coreValue (dotOperation parameters first second) point time)=
      (fun time => product (coreValue first point time) (coreValue second point time)) := by
    funext time
    exact (coreValue_pairProduct physicalDotProduct first second _ _).trans (physicalBilinear_apply _ _ _).symm
  rw [same] at original
  have identity := original.unique derivative
  rw [coreValue_add]
  change _=coreValue (pairProductLinear parameters physicalDotProduct (timeDerivativeCore parameters first) second) point axial+
    coreValue (pairProductLinear parameters physicalDotProduct first (timeDerivativeCore parameters second)) point axial
  rw [coreValue_pairProduct,coreValue_pairProduct]
  simpa only [product,physicalBilinear_apply] using identity

end Grad.OriginalKernelCovariantRecovery
