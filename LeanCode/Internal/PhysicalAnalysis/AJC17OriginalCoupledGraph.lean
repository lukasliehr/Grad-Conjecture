import AJC16SharedPhysicalWeakGraph
import AIV9LiteralWeightedGraphBounds
import AIW18OriginalLowBF6Consumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularStrongSolution
open Grad.CartesianState Grad.AnnularVariational Grad.AnnularCoupledInverse Grad.AnnularCrossMaps
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow Grad.AnnularHighTilt Grad.AnnularLowEnergy

private def hilbertPairEquiv {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (first : E ≃L[ℂ] F) (second : G ≃L[ℂ] H) : WithLp 2 (E × G) ≃L[ℂ] WithLp 2 (F × H) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E G).trans
    ((first.prodCongr second).trans (WithLp.prodContinuousLinearEquiv 2 ℂ F H).symm)

private theorem inversePairBound {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (first : E ≃L[ℂ] F) (second : G ≃L[ℂ] H) (a b radiusFactor : ℝ)
    (aNonnegative : 0 ≤ a) (bNonnegative : 0 ≤ b) (factorOne : 1 ≤ radiusFactor)
    (firstBound : ∀ x, ‖first.symm x‖ ≤ a * ‖x‖)
    (secondBound : ∀ x, ‖second.symm x‖ ≤ b * radiusFactor * ‖x‖)
    (field : WithLp 2 (F × H)) :
    ‖(hilbertPairEquiv first second).symm field‖ ≤ (a + b) * radiusFactor * ‖field‖ := by
  let out := (hilbertPairEquiv first second).symm field
  have outSq := WithLp.prod_norm_sq_eq_of_L2 out
  have inSq := WithLp.prod_norm_sq_eq_of_L2 field
  change ‖out‖ ^ 2 = ‖out.ofLp.1‖ ^ 2 + ‖out.ofLp.2‖ ^ 2 at outSq
  change ‖field‖ ^ 2 = ‖field.ofLp.1‖ ^ 2 + ‖field.ofLp.2‖ ^ 2 at inSq
  have highLe : ‖field.ofLp.1‖ ≤ ‖field‖ := by
    nlinarith [norm_nonneg field, norm_nonneg field.ofLp.1, sq_nonneg ‖field.ofLp.2‖]
  have lowLe : ‖field.ofLp.2‖ ≤ ‖field‖ := by
    nlinarith [norm_nonneg field, norm_nonneg field.ofLp.2, sq_nonneg ‖field.ofLp.1‖]
  have outSum : ‖out‖ ≤ ‖out.ofLp.1‖ + ‖out.ofLp.2‖ := by
    nlinarith [norm_nonneg out, norm_nonneg out.ofLp.1, norm_nonneg out.ofLp.2,
      mul_nonneg (norm_nonneg out.ofLp.1) (norm_nonneg out.ofLp.2)]
  have high : ‖out.ofLp.1‖ ≤ a * radiusFactor * ‖field‖ :=
    (firstBound field.ofLp.1).trans ((mul_le_mul_of_nonneg_left highLe aNonnegative).trans
      (mul_le_mul_of_nonneg_right (by nlinarith : a ≤ a * radiusFactor) (norm_nonneg field)))
  have low : ‖out.ofLp.2‖ ≤ b * radiusFactor * ‖field‖ :=
    (secondBound field.ofLp.2).trans (mul_le_mul_of_nonneg_left lowLe (by positivity))
  exact outSum.trans ((add_le_add high low).trans_eq (by ring))

/-- Original AK retained high graph and original AJ low graph, with their
original Hilbert norms. The equivalence below uses the accepted BF6 maps. -/
abbrev OriginalCoupledSpace (lower L : ℝ) (positive : 0 < lower) :=
  WithLp 2 (OriginalHighSpace lower L positive × originalLowGraph lower)

def originalCoupledEquivalence (parameters : PhaseParameters) (lower L : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < L) :
    OriginalCoupledSpace lower L positive ≃L[ℂ] CoupledSpace lower L positive lengthPositive :=
  hilbertPairEquiv (originalHighTiltEquivalence lower L positive bounded lengthPositive)
    (originalLowGraphEquivalence parameters lower L positive lengthPositive bounded)

def originalCoupledUnweightConstant (parameters : PhaseParameters) (L : ℝ) : ℝ :=
  (5 + L⁻¹ + highTiltExponent) + 3 * originalLowToAJConstant parameters L

theorem originalCoupledUnweightConstant_nonnegative (parameters : PhaseParameters) (L : ℝ)
    (lengthPositive : 0 < L) : 0 ≤ originalCoupledUnweightConstant parameters L := by
  have low := (originalLowToAJConstant_dominates parameters L lengthPositive).2.2.2
  unfold originalCoupledUnweightConstant highTiltExponent
  positivity

/-- The only inverse coordinate loss is ell^-1 in the original low graph.
Every constant is fixed before the collar or the coefficient state. -/
theorem originalCoupledEquivalence_inverse_bound (parameters : PhaseParameters) (lower L : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < L)
    (field : CoupledSpace lower L positive lengthPositive) :
    ‖(originalCoupledEquivalence parameters lower L positive bounded lengthPositive).symm field‖ ≤
      originalCoupledUnweightConstant parameters L * lower⁻¹ * ‖field‖ := by
  have low := (originalLowToAJConstant_dominates parameters L lengthPositive).2.2.2
  have highNonnegative : 0 ≤ 5 + L⁻¹ + highTiltExponent := by unfold highTiltExponent; positivity
  have factorOne : 1 ≤ lower⁻¹ := (one_le_inv₀ positive).mpr bounded
  exact inversePairBound (originalHighTiltEquivalence lower L positive bounded lengthPositive)
    (originalLowGraphEquivalence parameters lower L positive lengthPositive bounded)
    (5 + L⁻¹ + highTiltExponent) (3 * originalLowToAJConstant parameters L) lower⁻¹
    highNonnegative (by positivity) factorOne
    (originalHighTilt_inverse_bound lower L positive bounded lengthPositive)
    (originalLowGraphEquivalence_inverse_bound parameters lower L positive lengthPositive bounded) field

end Grad.AnnularStrongSolution
