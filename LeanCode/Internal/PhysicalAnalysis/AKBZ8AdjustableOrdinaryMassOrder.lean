import AKBZ7OriginalMixedPureEndpointEstimate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 850000
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.FourierInterpolation
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Algebra

theorem ordinaryMassRow_zero {dimension : ℕ} (mass : ℝ) (field : ClosedJet dimension) :
    apMassRow mass 0 field=apMassRow 1 0 field := by
  apply PiLp.ext
  intro index
  change (mass:ℂ)^(0-derivativeOrder index) • _=(1:ℂ)^(0-derivativeOrder index) • _
  rw [Nat.zero_sub,pow_zero,one_pow]

/-- CT7 for each SAME ordinary weighted cell row. Adjustable constants are
uniform for every mass at least one, including the original zero Fourier cell. -/
theorem ordinaryMassOrder_adjustable
    (grade order : ℕ) (orderPositive : 0<order) (orderTop : order<grade)
    (epsilon : ℝ) (epsilonPositive : 0<epsilon) :
    ∃ remainder : ℝ, 0≤remainder ∧ ∀ (dimension : ℕ) (mass : ℝ), 1≤mass →
      ∀ field : ClosedJet dimension,
      mass^(grade-order)*‖apMassRow 1 order field‖≤epsilon*‖apMassRow 1 grade field‖+
        remainder*(mass^grade*‖apMassRow mass 0 field‖) := by
  let theta := interpolationTheta 0 order grade
  have thetaPositive : 0<theta := interpolationTheta_pos orderPositive orderTop
  have thetaOne : theta<1 := interpolationTheta_lt_one orderPositive orderTop
  obtain ⟨remainder,nonnegative,adjust⟩ := positiveOrder_adjustable_constant (1-theta)
    (originalInterpolationConstant 0 order grade) epsilon (sub_pos.mpr thetaOne)
    (by linarith) (originalInterpolationConstant_nonnegative _ _ _) epsilonPositive
  refine ⟨remainder,nonnegative,?_⟩
  intro dimension mass massOne field
  have massPositive : 0<mass := zero_lt_one.trans_le massOne
  have bound := mul_le_mul_of_nonneg_left (apOrdinaryRow_interpolation orderPositive orderTop field)
    (pow_nonneg massPositive.le (grade-order))
  have power : mass^(grade-order)=(mass^grade)^(1-theta) := by
    simpa only [Nat.sub_zero] using apMassPower_complement mass massPositive orderPositive orderTop
  have rearrange :
      mass^(grade-order)*(originalInterpolationConstant 0 order grade*
        (‖apMassRow 1 0 field‖^(1-theta)*‖apMassRow 1 grade field‖^theta))=
      originalInterpolationConstant 0 order grade*
        (‖apMassRow 1 grade field‖^(1-(1-theta))*(mass^grade*‖apMassRow 1 0 field‖)^(1-theta)) := by
    rw [Real.mul_rpow (pow_nonneg massPositive.le _) (norm_nonneg _),←power,
      show 1-(1-theta)=theta by ring]
    ring
  have result := bound.trans (rearrange.le.trans
    (adjust ‖apMassRow 1 grade field‖ (mass^grade*‖apMassRow 1 0 field‖)
      (norm_nonneg _) (mul_nonneg (pow_nonneg massPositive.le _) (norm_nonneg _))))
  rw [ordinaryMassRow_zero]
  exact result

end Grad.OriginalCartesianTameEstimate
