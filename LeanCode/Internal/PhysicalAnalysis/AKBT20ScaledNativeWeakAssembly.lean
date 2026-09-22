import AKBT19ActualNativeCorrectionIdentities

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets Grad.SpatialDilation
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra

/-- Normalization of the SAME three scaled native equations into the eight
ER carriers. The sign and original length in the scalar correction are kept. -/
theorem nativeERRows_scaledWeak (scale : Scale) (length : ℝ) (lengthNonzero : length ≠ 0)
    (covariant force cofactor : StartupMoments 3) (xi knownThird determinant : StartupMoments 1)
    (knownForce : StartupMoments 2)
    (mean : ∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test)
      ((scale.val : ℂ)⁻¹ • startupMomentDilation scale xi.field) = 0)
    (forceEquation : StartupWeakProjectedForceEquation ((scale.val : ℂ)⁻¹ • startupMomentDilation scale xi.field)
      (startupMomentDilation scale (originalValueKernel planarPartMap covariant.field))
      (startupMomentDilation scale (startupGenuineQradKernel
        (knownForce.field-(2 : ℂ) • originalValueKernel planarPartMap force.field))))
    (thirdEquation : StartupWeakThirdEquation (fun cell => (scale.val : ℂ) * ((Complex.I * (cell : ℂ))/(length : ℂ)))
      ((scale.val : ℂ)⁻¹ • startupMomentDilation scale (startupTrueAngularInverse 1 0 xi.field))
      (startupMomentDilation scale (originalValueKernel toroidalPartMap covariant.field))
      (startupMomentDilation scale ((length : ℂ)⁻¹ •
        (knownThird.field-(-2*(length : ℂ)) • originalScalarMeanFreeKernel (originalValueKernel toroidalPartMap force.field)))))
    (determinantEquation : StartupWeakDeterminantEquation (fun cell => (scale.val : ℂ) * ((Complex.I * (cell : ℂ))/(length : ℂ)))
      (startupMomentDilation scale (originalValueKernel planarPartMap covariant.field))
      (startupMomentDilation scale (originalValueKernel toroidalPartMap covariant.field))
      ((scale.val : ℂ) • startupMomentDilation scale ((length : ℂ)⁻¹ • determinant.field))
      (startupMomentDilation scale ((originalValueKernel planarPartMap cofactor.field+originalValueKernel planarPartMap covariant.field)-
        originalAverageKernel (originalValueKernel planarPartMap cofactor.field+originalValueKernel planarPartMap covariant.field)))
      (startupMomentDilation scale (originalScalarMeanFreeKernel
        (originalValueKernel toroidalPartMap cofactor.field+originalValueKernel toroidalPartMap covariant.field)))) :
    StartupNativeWeakRows (scale.val/length) ((scale.val : ℂ)⁻¹ • startupMomentDilation scale xi.field)
      (nativeERRows (covariant.dilate scale) (force.dilate scale) (cofactor.dilate scale)
        (knownForce.dilate scale) ((knownThird.dilate scale).smul (length : ℂ)⁻¹)
        ((determinant.dilate scale).smul ((scale.val : ℂ)/(length : ℂ)))) := by
  have axial : (fun cell : ℤ => (scale.val : ℂ) * ((Complex.I*(cell : ℂ))/(length : ℂ))) =
      fun cell : ℤ => ((scale.val/length : ℝ) : ℂ)*(Complex.I*(cell : ℂ)) := by
    funext cell
    push_cast
    ring
  have lengthComplex : (length : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr lengthNonzero
  refine ⟨?_,?_,?_,mean⟩
  · change StartupWeakProjectedForceEquation _ (originalValueKernel planarPartMap (startupMomentDilation scale covariant.field))
      (startupGenuineQradKernel (startupMomentDilation scale knownForce.field)-
        (2 : ℂ) • startupGenuineQradKernel (originalValueKernel planarPartMap (startupMomentDilation scale force.field)))
    simpa only [startupGenuineQradKernel_dilation,startupMomentDilation_sub,startupMomentDilation_smul,
      originalValueKernel_dilation,map_sub,map_smul] using forceEquation
  · change StartupWeakThirdEquation _ (originalScalarInverseKernel _)
      (originalValueKernel toroidalPartMap (startupMomentDilation scale covariant.field))
      ((length : ℂ)⁻¹ • startupMomentDilation scale knownThird.field+
        (2 : ℂ) • originalScalarMeanFreeKernel (originalValueKernel toroidalPartMap (startupMomentDilation scale force.field)))
    rw [axial,originalValueKernel_dilation,startupMomentDilation_smul,startupMomentDilation_sub,
      startupMomentDilation_smul,originalScalarMeanFreeKernel_dilation,originalValueKernel_dilation,
      startupTrueAngularInverse_dilation,smul_sub,smul_smul] at thirdEquation
    have scalar : (length : ℂ)⁻¹*(-2*(length : ℂ)) = -2 := by field_simp [lengthComplex]
    rw [scalar,neg_smul,sub_neg_eq_add] at thirdEquation
    simpa only [originalScalarInverseKernel,map_smul] using thirdEquation
  · change StartupWeakDeterminantEquation _
      (originalValueKernel planarPartMap (startupMomentDilation scale covariant.field))
      (originalValueKernel toroidalPartMap (startupMomentDilation scale covariant.field))
      (((scale.val : ℂ)/(length : ℂ)) • startupMomentDilation scale determinant.field)
      (originalValueKernel planarPartMap (startupMomentDilation scale cofactor.field+startupMomentDilation scale covariant.field)-
        originalAverageKernel (originalValueKernel planarPartMap (startupMomentDilation scale cofactor.field+startupMomentDilation scale covariant.field)))
      (originalScalarMeanFreeKernel (originalValueKernel toroidalPartMap
        (startupMomentDilation scale cofactor.field+startupMomentDilation scale covariant.field)))
    rw [axial] at determinantEquation
    simpa only [originalValueKernel_dilation,startupMomentDilation_smul,smul_smul,div_eq_mul_inv,
      startupMomentDilation_sub,originalAverageKernel_dilation,startupMomentDilation_add,
      originalScalarMeanFreeKernel_dilation,map_add] using determinantEquation

end Grad.CartesianStartup
