import AKDR8SameOriginalTangentialPolynomial
import AKDB4SameWeightedNativeScalar

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.CartesianStartup Grad.PDEBootstrap Grad.GenericCarriers
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.ActualOriginalSourceMoments
open Grad.NonlinearProduct Grad.NonlinearQuotientBounds Grad.SourceBoundaryTrace

theorem originalSourceFieldLinear_injective {dimension : ℕ} (parameters : PhaseParameters) :
    Function.Injective (originalSourceFieldLinear (dimension := dimension) parameters) := by
  intro first second equality
  apply Subtype.ext
  funext cell
  apply phaseWeightedJet_injective parameters cell
  apply closedJet_eq_of_value_eq
  apply Grad.GaugeCoefficients.Physical.Compensated.closedValueL2_injective dimension
  change closedContinuousToDiskL2 (phaseWeightedJet parameters cell (first.val cell)).value =
    closedContinuousToDiskL2 (phaseWeightedJet parameters cell (second.val cell)).value
  apply Lp.ext
  filter_upwards [originalSource_field_closed parameters first,originalSource_field_closed parameters second,
    closedContinuousToDiskL2_ae (phaseWeightedJet parameters cell (first.val cell)).value,
    closedContinuousToDiskL2_ae (phaseWeightedJet parameters cell (second.val cell)).value] with point one two left right
  rw [left,right,← one cell,← two cell]
  exact congrArg (fun field : StartupL2 dimension => field point cell) equality

def originalRetainedScalarCore (parameters : PhaseParameters)
    (vector right : ACore parameters 2) : ACore parameters 1 :=
  tangentialBoundaryCore parameters (originalRecoveredGradientCore parameters vector right)

theorem originalRetainedScalarCore_bound (parameters : PhaseParameters)
    (vector right : ACore parameters 2) (grade : ℕ) :
    originalGradeNorm grade (originalRetainedScalarCore parameters vector right) ≤
      tangentialBoundaryConstant grade *
        (originalRecoveredGradientConstant grade * originalGradeNorm grade vector +
          originalCovariantPrimitiveConstant grade * originalGradeNorm grade right) :=
  (tangentialBoundaryCore_bound parameters grade _).trans
    (mul_le_mul_of_nonneg_left (originalRecoveredGradientCore_bound parameters vector right grade)
      (tangentialBoundaryConstant_nonnegative grade))

theorem originalRetainedScalarCore_sameField (parameters : PhaseParameters)
    (vector right : ACore parameters 2) :
    originalSourceFieldLinear parameters (originalRetainedScalarCore parameters vector right) =
      startupTangentialPolynomialKernel
        (startupRecoveredGradient (originalSourceFieldLinear parameters vector)
          (originalSourceFieldLinear parameters right)) := by
  rw [originalRetainedScalarCore,originalTangentialPolynomial_sameField,
    originalRecoveredGradientCore_sameField]

/-- The retained scalar is the SAME weighted native solution. Its estimate
uses the actual weak equation and the original radial phase, without a
regularity or new scalar-recovery premise. -/
theorem actualRetainedScalarCore_bound (parameters : PhaseParameters)
    {scale : ℝ} {psi : StartupL2 1} {weighted original : StartupNativeERRows}
    (weak : StartupNativeWeakRows scale psi original)
    {symbol : ℤ → Spatial → ℝ} (same : StartupNativeERRowsRelated symbol weighted original)
    (radial : ∀ cell (first second : Spatial), ‖first‖=‖second‖ → symbol cell first=symbol cell second)
    (scalar : ACore parameters 1) (vector right : ACore parameters 2)
    (scalarSame : StartupRadialRelated symbol (originalSourceFieldLinear parameters scalar) psi)
    (vectorSame : originalSourceFieldLinear parameters vector = weighted.vector.field)
    (rightSame : originalSourceFieldLinear parameters right = weighted.knownForce.field-weighted.forceCorrection.field)
    (grade : ℕ) :
    originalGradeNorm grade scalar ≤ tangentialBoundaryConstant grade *
      (originalRecoveredGradientConstant grade * originalGradeNorm grade vector +
        originalCovariantPrimitiveConstant grade * originalGradeNorm grade right) := by
  have native := weak.weighted_scalar_polynomial same radial scalarSame
  have recovered := originalRetainedScalarCore_sameField parameters vector right
  rw [vectorSame,rightSame] at recovered
  have identity : scalar = originalRetainedScalarCore parameters vector right :=
    originalSourceFieldLinear_injective parameters (native.trans recovered.symm)
  rw [identity]
  exact originalRetainedScalarCore_bound parameters vector right grade

end Grad.OriginalCoreRealization
