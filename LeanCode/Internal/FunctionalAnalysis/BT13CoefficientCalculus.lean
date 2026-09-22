import BT12RadialJets
import CompactSmoothIntegral

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.BoundaryTrace

open Grad.ClosedJets Grad.CartesianState Grad.Constraints

local instance coefficientCalculusPeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

theorem cellExponential_smooth (mode : ℤ) : ContDiff ℝ ∞ (cellExponential mode) := by
  unfold cellExponential
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

theorem angularCoefficient_compact {dimension : ℕ} (field : ℝ → ComplexEuclidean dimension) (mode : ℤ) :
    angularCoefficient field mode = (2 * Real.pi)⁻¹ •
      ∫ angle in Icc (-Real.pi) Real.pi, cellExponential (-mode) angle • field angle := by
  rw [angularCoefficient_integral, intervalIntegral.integral_of_le (neg_lt_self Real.pi_pos).le,
    ← integral_Icc_eq_integral_Ioc]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with angle
  rw [show fourier (-mode) (angle : CellCircle) = cellExponential (-mode) angle from cellCharacter_coe _ _]

def angularIntegrand {dimension : ℕ} (field : ℝ × ℝ → ComplexEuclidean dimension)
    (mode : ℤ) (point : ℝ × ℝ) : ComplexEuclidean dimension :=
  cellExponential (-mode) point.2 • field point

theorem angularIntegrand_smooth {dimension : ℕ} (field : ℝ × ℝ → ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ field) (mode : ℤ) : ContDiff ℝ ∞ (angularIntegrand field mode) :=
  ((cellExponential_smooth (-mode)).comp contDiff_snd).smul smooth

theorem angularCoefficient_smooth {dimension : ℕ} (field : ℝ × ℝ → ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ field) (mode : ℤ) :
    ContDiff ℝ ∞ (fun time => angularCoefficient (fun angle => field (time, angle)) mode) := by
  have integrandSmooth : ContDiffOn ℝ ∞ (angularIntegrand field mode)
      ((univ : Set ℝ) ×ˢ univ) := (angularIntegrand_smooth field smooth mode).contDiffOn
  have compactSmooth := contDiffOn_compactIntegral isOpen_univ integrandSmooth (-Real.pi) Real.pi
  apply contDiffOn_univ.mp
  simp_rw [angularCoefficient_compact]
  exact (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ => (2 * Real.pi)⁻¹) univ).smul compactSmooth

theorem angularCoefficient_hasDerivAt {dimension : ℕ} (field : ℝ × ℝ → ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ field) (mode : ℤ) (time : ℝ) :
    HasDerivAt (fun radial => angularCoefficient (fun angle => field (radial, angle)) mode)
      (angularCoefficient (fun angle => radialField field (time, angle)) mode) time := by
  let integrand := angularIntegrand field mode
  have integrandSmooth : ContDiff ℝ ∞ integrand := angularIntegrand_smooth field smooth mode
  have derivative := hasFDerivAt_compactIntegral isOpen_univ
    (integrandSmooth.contDiffOn : ContDiffOn ℝ ∞ integrand ((univ : Set ℝ) ×ˢ univ))
    (-Real.pi) Real.pi time (mem_univ time)
  have derivativeContinuous : Continuous (integralParameterDerivative integrand) :=
    ((contDiff_infty_iff_fderiv.mp integrandSmooth).2.clm_comp contDiff_const).continuous
  have derivativeIntegrable : IntegrableOn (fun angle : ℝ => integralParameterDerivative integrand (time, angle))
      (Icc (-Real.pi) Real.pi) :=
    (derivativeContinuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_Icc
  have pointwise : ∀ angle : ℝ, integralParameterDerivative integrand (time, angle) 1 =
      cellExponential (-mode) angle • radialField field (time, angle) := by
    intro angle
    rw [integralParameterDerivative_eq time angle (integrandSmooth.differentiable (by simp) _)]
    have sectionDerivative := (radialField_hasDerivAt field smooth time angle).const_smul (cellExponential (-mode) angle)
    have equality := congrArg (fun linear : ℝ →L[ℝ] ComplexEuclidean dimension => linear 1) sectionDerivative.hasFDerivAt.fderiv
    change (fderiv ℝ (fun source => integrand (source, angle)) time) 1 =
      (ContinuousLinearMap.toSpanSingleton ℝ (cellExponential (-mode) angle • radialField field (time, angle))) 1 at equality
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using equality
  have functionEquality : (fun radial => angularCoefficient (fun angle => field (radial, angle)) mode) =
      fun radial => (2 * Real.pi)⁻¹ • ∫ angle in Icc (-Real.pi) Real.pi, integrand (radial, angle) := by
    funext radial
    exact angularCoefficient_compact _ _
  rw [functionEquality]
  apply (derivative.hasDerivAt.const_smul ((2 * Real.pi)⁻¹)).congr_deriv
  change (2 * Real.pi)⁻¹ • ((∫ angle in Icc (-Real.pi) Real.pi,
    integralParameterDerivative integrand (time, angle)) 1) = _
  rw [angularCoefficient_compact]
  congr 1
  rw [ContinuousLinearMap.integral_apply derivativeIntegrable]
  apply integral_congr_ae
  filter_upwards [] with angle
  exact pointwise angle

end Grad.BoundaryTrace
