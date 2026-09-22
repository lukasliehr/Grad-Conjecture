import AKDT24ActualNormalShape

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalGeometry
open Grad.MainTarget
open Grad.MainAssembly.PhysicalSimilarityRigidity Grad.MainAssembly.SampledPhysicalSimilarityRigidity
open Grad.MainAssembly.PhysicalHessianCovariance Grad.MainAssembly.NormalHessianCovariance
open Grad.MainAssembly.CircleIsometryClassification Grad.MainAssembly.TensorAngleRigidity

/-- Pressure preservation transports the actual normalized tensor into the
two-sign angular congruence. Both magnetic signs remain allowed. -/
theorem preserved_normal_shape_angle_congruence
    (configuration : Representative) (radius rho alpha delta parameter : ℝ) (period : ℕ)
    (rhoPositive : 0 < rho)
    (shape : HasPrescribedNormalShape configuration radius rho (sampledAlphaAngle period alpha delta parameter))
    (pressure : Vec → ℝ) (pressureNear : SmoothNear (range configuration.position) pressure)
    (represents : ∀ reference, pressure (configuration.position reference) = configuration.pressure reference)
    (axisInterior : roundAxis radius ⊆ interior (range configuration.position))
    (orthogonal : Vec ≃ₗᵢ[ℝ] Vec)
    (preserves : ∀ point ∈ range configuration.position, pressure (orthogonal point) = pressure point)
    (tangentSign verticalSign shift : ℝ) (verticalSignValue : verticalSign = 1 ∨ verticalSign = -1)
    (radialAction : ∀ time, orthogonal (axisRadial time) = axisRadial (tangentSign * time + shift))
    (verticalAction : orthogonal axisVertical = verticalSign • axisVertical) :
    ∀ time, ∃ integer : ℤ,
      sampledAlphaAngle period alpha delta parameter (tangentSign * time + shift) -
        verticalSign * sampledAlphaAngle period alpha delta parameter time = (integer : ℝ) * Real.pi := by
  obtain ⟨canonicalPressure, canonicalRepresents, canonicalShape⟩ := shape
  have axisMem (time : ℝ) : radius • axisRadial time ∈ roundAxis radius := by
    refine ⟨time, ?_⟩
    ext coordinate
    fin_cases coordinate <;> simp [axisRadial, vector]
  intro time
  let targetTime := tangentSign * time + shift
  have sourceInterior := axisInterior (axisMem time)
  have targetInterior := axisInterior (axisMem targetTime)
  have scaledOne : (scaledOrthogonal 1 one_ne_zero orthogonal).toContinuousLinearMap = orthogonal.toContinuousLinearMap := by
    ext direction
    simp
  have ambientCovariance :
      (pressureHessian pressure (orthogonal (radius • axisRadial time))).compContinuousLinearMap
        (fun _ => orthogonal.toContinuousLinearMap) = (1 : ℝ) ^ 2 • pressureHessian pressure (radius • axisRadial time) := by
    simpa only [one_smul, zero_add, add_zero, scaledOne] using
      pressureHessian_scaled_covariance (range configuration.position) pressure pressure 1 1 orthogonal 0 0
        zero_lt_one pressureNear (by simpa using preserves) (radius • axisRadial time) sourceInterior
  have sourceEquality := pressureHessian_eq_of_represents configuration pressure canonicalPressure
    represents canonicalRepresents (radius • axisRadial time) sourceInterior
  have targetEquality := pressureHessian_eq_of_represents configuration pressure canonicalPressure
    represents canonicalRepresents (radius • axisRadial targetTime) targetInterior
  have sourceNormal : normalHessianMatrix pressure radius time = normalHessianMatrix canonicalPressure radius time := by
    unfold normalHessianMatrix
    rw [sourceEquality]
  have targetNormal : normalHessianMatrix pressure radius targetTime = normalHessianMatrix canonicalPressure radius targetTime := by
    unfold normalHessianMatrix
    rw [targetEquality]
  have signedCovariance := signed_normalHessian_covariance pressure pressure radius time targetTime
    1 verticalSign orthogonal (radialAction time) verticalAction ambientCovariance
  rw [sourceNormal, targetNormal] at signedCovariance
  have normalizedCovariance := normalizedInverseShape_signed_covariance
    (normalHessianMatrix canonicalPressure radius time) (normalHessianMatrix canonicalPressure radius targetTime)
    ((1 : ℝ) ^ 2) verticalSign (by norm_num) verticalSignValue (canonicalShape time).1 signedCovariance
  rw [(canonicalShape time).2, (canonicalShape targetTime).2] at normalizedCovariance
  exact Grad.MainAssembly.TensorAngleRigidity.Consumer.angle_congruence_of_signed_tensor_covariance rho
    (sampledAlphaAngle period alpha delta parameter time) (sampledAlphaAngle period alpha delta parameter targetTime)
    verticalSign rhoPositive verticalSignValue normalizedCovariance

end Grad.PhysicalGeometry
