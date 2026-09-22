import AKU30OriginalLiftAxisJetsAndSupport
import AKU28ActualLiftLeadingFourierIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.CompletedReality
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger Grad.NonlinearDivision

theorem originalFourierPhase_eq_axial : fourierPhase = axialPhase := by
  funext cell angle
  exact ((axialPhase_eq_character cell angle).trans (cellCharacter_coe cell angle)).symm

/-- Equality of actual physical axis fields recovers every original Fourier
coefficient, including cell zero. -/
theorem axisPhysicalValue_ext {parameters : PhaseParameters} {dimension : ℕ}
    {first second : Grad.AxisCore.AxisSmoothCore parameters dimension}
    (same : ∀ angle, axisPhysicalValue first angle = axisPhysicalValue second angle) : first = second := by
  apply Subtype.ext
  apply axialSeries_ext first.val second.val (axisData_value_norm_summable first)
    (axisData_value_norm_summable second)
  simpa only [axisPhysicalValue,originalFourierPhase_eq_axial] using same

theorem traceZero_physical {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (angle : ℝ) :
    axisPhysicalValue (traceZero field) angle = coreValue field closedOrigin angle := by
  unfold axisPhysicalValue coreValue
  rw [originalFourierPhase_eq_axial]
  rfl

def fixedProfileValueMap {input output : ℕ}
    (profile : ComplexEuclidean input →ₗ[ℂ] ClosedJet output) (point : ClosedDisk) :
    ComplexEuclidean input →L[ℂ] ComplexEuclidean output :=
  LinearMap.toContinuousLinearMap
    { toFun := fun value => (profile value).value point
      map_add' := by
        intro first second
        rw [map_add,closedJet_value_add,ContinuousMap.add_apply]
      map_smul' := by
        intro scalar value
        rw [map_smul,closedJet_value_smul,ContinuousMap.smul_apply]
        rfl }

theorem vectorAxisProfileCore_physical {parameters : PhaseParameters} {input output : ℕ}
    (profile : ComplexEuclidean input →ₗ[ℂ] ClosedJet output)
    (data : Grad.AxisCore.AxisSmoothCore parameters input) (point : ClosedDisk) (angle : ℝ) :
    coreValue (vectorAxisProfileCore profile data) point angle =
      (profile (axisPhysicalValue data angle)).value point := by
  have total := (fixedProfileValueMap profile point).hasSum (axisPhysicalValue_hasSum data angle)
  apply (coreValue_summable (vectorAxisProfileCore profile data) point angle).hasSum.unique
  apply total.congr_fun
  intro cell
  rw [originalFourierPhase_eq_axial,vectorAxisProfileCore_val]
  exact ((fixedProfileValueMap profile point).map_smul _ _).symm

/-- Actual core differentiation acts on the fixed profile, with no axis
coefficient differentiation and no change of cell coefficients. -/
theorem partialCore_vectorAxisProfileCore {parameters : PhaseParameters} {input output : ℕ}
    (profile : ComplexEuclidean input →ₗ[ℂ] ClosedJet output)
    (data : Grad.AxisCore.AxisSmoothCore parameters input) (direction : Fin 2) :
    partialCore parameters direction (vectorAxisProfileCore profile data) =
      vectorAxisProfileCore ((Grad.GaugeCoefficients.Physical.Compensated.partialJetLinear output direction).comp profile) data := by
  apply Subtype.ext
  funext cell
  rw [partialCore_val,vectorAxisProfileCore_val,vectorAxisProfileCore_val]
  rfl

end Grad.FinitePhysicalJetLift
