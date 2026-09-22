import AKAT25OriginalCartesianForceConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.ActualDeterminantEquations

/-- The literal AD13--AD17 reversal. The two projected force values remain
inside their respective kappa products throughout the cancellation. -/
theorem correctedFlux_sourceCancellation (radius length : ℂ)
    (radiusNonzero : radius ≠ 0) (lengthNonzero : length ≠ 0)
    (m1 m1Radial m3Axial q qRadial qAngular qAxial : ℂ)
    (kappa : Fin 3 → ℂ) (kappaRadial kappaAxial angularKappaPairing : ℂ)
    (forceZero projectedForceOne projectedForceTwo : ℂ)
    (sourceZero sourceOne sourceTwo : ℂ) (rotated : Fin 3 → ℂ)
    (first : rotated 0 = q+radius*qRadial+projectedForceOne-sourceOne)
    (second : rotated 1 = qAngular+forceZero-sourceZero)
    (third : rotated 2 = radius/length*qAxial-projectedForceTwo+sourceTwo) :
    (m1Radial+kappaRadial*q+kappa 0*qRadial) +
      (m1+kappa 0*q)/radius +
      (m3Axial+kappaAxial*q+kappa 2*qAxial)/length +
      (kappa 1*qAngular+
        (angularKappaPairing+kappa 0*projectedForceOne+kappa 1*forceZero-kappa 2*projectedForceTwo)-
        radius*kappaRadial*q-radius/length*kappaAxial*q)/radius -
      (kappa 0*sourceOne+kappa 1*sourceZero-kappa 2*sourceTwo)/radius =
    m1Radial+m1/radius+
      (angularKappaPairing+kappa 0*rotated 0+kappa 1*rotated 1+kappa 2*rotated 2)/radius+m3Axial/length := by
  rw [first,second,third]
  field_simp [radiusNonzero,lengthNonzero]
  ring

/-- Genuine differentiation of the corrected radial flux before its outer
angular projection; q is the SAME Xi/r field. -/
theorem correctedRadialFlux_hasDerivAt (m kappa q : ℝ → ℂ) (radius : ℝ)
    (mRadial kappaRadial qRadial : ℂ)
    (mDerivative : HasDerivAt m mRadial radius)
    (kappaDerivative : HasDerivAt kappa kappaRadial radius)
    (qDerivative : HasDerivAt q qRadial radius) :
    HasDerivAt (fun value => m value+kappa value*q value)
      (mRadial+kappaRadial*q radius+kappa radius*qRadial) radius := by
  simpa only [Pi.add_def,Pi.mul_def,add_assoc] using mDerivative.add (kappaDerivative.mul qDerivative)

end Grad.ActualDeterminantEquations
