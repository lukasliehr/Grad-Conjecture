import NormalHessianCovariance
import TensorAngleRigidityConsumer
import HarmonicRigidityConsumer

noncomputable section

namespace Grad.MainAssembly.PhysicalSimilarityRigidity

open Set
open Grad.MainTarget
open Grad.MainAssembly.TargetPhysicalSimilarity
open Grad.MainAssembly.PhysicalHessianCovariance
open Grad.MainAssembly.NormalHessianCovariance
open Grad.MainAssembly.RoundAxisSimilarity
open Grad.MainAssembly.CircleIsometryClassification
open Grad.MainAssembly.TensorAngleRigidity
open Grad.MainAssembly.HarmonicRigidity

/-- Concrete geometric input still owed by the analytic construction: one
ambient pressure representing the target pressure has the prescribed
invertible trace-normalized normal Hessian at every axis angle. -/
def HasPrescribedNormalShape (representative : Representative)
    (radius rho : ℝ) (angle : ℝ → ℝ) : Prop :=
  ∃ pressure : Vec → ℝ,
    (∀ point : Reference,
      pressure (representative.position point) = representative.pressure point) ∧
    ∀ time,
      IsUnit (-(normalHessianMatrix pressure radius time)).det ∧
      normalizedInverseShape (normalHessianMatrix pressure radius time) =
        normalizedShape rho (angle time)

private theorem axisPoint_mem (radius angle : ℝ) :
    radius • axisRadial angle ∈ roundAxis radius := by
  refine ⟨angle, ?_⟩
  ext coordinate
  fin_cases coordinate <;> simp [axisRadial, vector]

/-- Exact NG_R17 consumer once the concrete family's normal-shape formula is
available. It uses the entire physical similarity, fixes its affine scale and
translation from the common round axis, removes the nonzero amplitude by
trace normalization, and invokes the accepted tensor-angle and two-harmonic
rigidity blocks. -/
theorem parameter_eq_of_physicalSimilarity
    (first second : Representative) (cellLength : ℝ) (period : ℕ)
    (rho alpha delta firstParameter secondParameter : ℝ)
    (axisRadiusPositive : 0 < period * cellLength)
    (rhoPositive : 0 < rho)
    (firstParameterPositive : 0 < firstParameter)
    (secondParameterPositive : 0 < secondParameter)
    (deltaNonzero : delta ≠ 0)
    (alphaNotLattice : ∀ integer : ℤ,
      2 * alpha ≠ (integer : ℝ) * Real.pi)
    (firstShape : HasPrescribedNormalShape first (period * cellLength) rho
      (alphaAngle alpha delta firstParameter))
    (secondShape : HasPrescribedNormalShape second (period * cellLength) rho
      (alphaAngle alpha delta secondParameter))
    (similarity : PhysicalSimilarity first second cellLength period) :
    secondParameter = firstParameter := by
  rcases firstShape with
    ⟨firstCanonicalPressure, firstCanonicalRepresents, firstCanonicalShape⟩
  rcases secondShape with
    ⟨secondCanonicalPressure, secondCanonicalRepresents, secondCanonicalShape⟩
  rcases similarity with
    ⟨spatialScale, amplitude, orthogonal, translation, pressureOffset,
      firstMagnetic, secondMagnetic, firstPressure, secondPressure,
      scalePositive, amplitudeNonzero,
      firstMagneticSmooth, firstPressureSmooth,
      secondMagneticSmooth, secondPressureSmooth,
      firstRepresents, secondRepresents,
      firstAxisInterior, secondAxisInterior,
      bodyEquality, axisEquality, magneticEquality, pressureEquality⟩
  have fixed := roundAxis_similarity_same_radius (period * cellLength)
    spatialScale orthogonal translation axisRadiusPositive scalePositive
    axisEquality
  rcases fixed with ⟨scaleOne, translationZero⟩
  subst spatialScale
  subst translation
  have axisEquality' :
      (fun point : Vec => orthogonal point + 0) ''
          roundAxis (period * cellLength) = roundAxis (period * cellLength) := by
    simpa using axisEquality
  rcases circleIsometryClassification (period * cellLength) orthogonal 0
      axisRadiusPositive axisEquality' with
    ⟨_, tangentSign, verticalSign, angleShift,
      tangentSignValue, verticalSignValue, radialAction, tangentAction,
      verticalAction, determinant⟩
  have angleCongruence : ∀ time, ∃ integer : ℤ,
      alphaAngle alpha delta secondParameter
            (tangentSign * time + angleShift) -
          verticalSign * alphaAngle alpha delta firstParameter time =
        (integer : ℝ) * Real.pi := by
    intro time
    let targetTime := tangentSign * time + angleShift
    have sourcePointInterior :
        (period * cellLength) • axisRadial time ∈
          interior (Set.range first.position) :=
      firstAxisInterior (axisPoint_mem (period * cellLength) time)
    have targetPointInterior :
        (period * cellLength) • axisRadial targetTime ∈
          interior (Set.range second.position) :=
      secondAxisInterior (axisPoint_mem (period * cellLength) targetTime)
    have scaledOne :
        (scaledOrthogonal 1 one_ne_zero orthogonal).toContinuousLinearMap =
          orthogonal.toContinuousLinearMap := by
      ext direction
      simp
    have ambientCovariance :
        (pressureHessian secondPressure
            (orthogonal ((period * cellLength) • axisRadial time))).compContinuousLinearMap
            (fun _ => orthogonal.toContinuousLinearMap) =
          amplitude ^ 2 • pressureHessian firstPressure
            ((period * cellLength) • axisRadial time) := by
      simpa only [one_smul, zero_add, add_zero, scaledOne] using
        pressureHessian_scaled_covariance
          (Set.range first.position) firstPressure secondPressure
          1 amplitude orthogonal 0 pressureOffset zero_lt_one firstPressureSmooth
          (by simpa using pressureEquality)
          ((period * cellLength) • axisRadial time) sourcePointInterior
    have sourceHessianEquality := pressureHessian_eq_of_represents first
      firstPressure firstCanonicalPressure
      (fun point => (firstRepresents point).2) firstCanonicalRepresents
      ((period * cellLength) • axisRadial time) sourcePointInterior
    have targetHessianEquality := pressureHessian_eq_of_represents second
      secondPressure secondCanonicalPressure
      (fun point => (secondRepresents point).2) secondCanonicalRepresents
      ((period * cellLength) • axisRadial targetTime) targetPointInterior
    have sourceNormalEquality :
        normalHessianMatrix firstPressure (period * cellLength) time =
          normalHessianMatrix firstCanonicalPressure (period * cellLength) time := by
      unfold normalHessianMatrix
      rw [sourceHessianEquality]
    have targetNormalEquality :
        normalHessianMatrix secondPressure (period * cellLength) targetTime =
          normalHessianMatrix secondCanonicalPressure (period * cellLength) targetTime := by
      unfold normalHessianMatrix
      rw [targetHessianEquality]
    have signedCovariance := signed_normalHessian_covariance
      firstPressure secondPressure (period * cellLength) time targetTime
      amplitude verticalSign orthogonal (radialAction time) verticalAction
      ambientCovariance
    rw [sourceNormalEquality, targetNormalEquality] at signedCovariance
    have normalizedCovariance := normalizedInverseShape_signed_covariance
      (normalHessianMatrix firstCanonicalPressure (period * cellLength) time)
      (normalHessianMatrix secondCanonicalPressure (period * cellLength) targetTime)
      (amplitude ^ 2) verticalSign (pow_ne_zero 2 amplitudeNonzero)
      verticalSignValue (firstCanonicalShape time).1 signedCovariance
    rw [(firstCanonicalShape time).2,
      (secondCanonicalShape targetTime).2] at normalizedCovariance
    exact TensorAngleRigidity.Consumer.angle_congruence_of_signed_tensor_covariance
      rho (alphaAngle alpha delta firstParameter time)
      (alphaAngle alpha delta secondParameter targetTime) verticalSign
      rhoPositive verticalSignValue normalizedCovariance
  exact (HarmonicRigidity.Consumer.full_two_parameter_two_sign_harmonic_rigidity
    alpha delta firstParameter secondParameter tangentSign verticalSign angleShift
    firstParameterPositive secondParameterPositive deltaNonzero alphaNotLattice
    tangentSignValue verticalSignValue angleCongruence).2.2.2

end Grad.MainAssembly.PhysicalSimilarityRigidity
