import GC10Interface

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 500000

open Set
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope
open scoped BigOperators ENNReal Topology

namespace Grad.GaugeCoefficients.Algebra

theorem coefficient_complete : CompletenessGoal L sigma gamma ell := by
  intro grade inputDimension outputDimension
  change IsComplete (Set.univ : Set
    ((smoothCore L sigma gamma ell grade inputDimension outputDimension).topologicalClosure))
  exact isComplete_univ

theorem finiteCellCore_dense : DenseCoreGoal L sigma gamma ell := by
  intro grade inputDimension outputDimension
  let core := smoothCore L sigma gamma ell grade inputDimension outputDimension
  change DenseRange (Set.inclusion (Submodule.le_topologicalClosure core))
  apply (denseRange_inclusion_iff (Submodule.le_topologicalClosure core)).2
  intro coefficient membership
  exact membership

theorem coefficient_norm_formula : NormFormulaGoal L sigma gamma ell := by
  intro grade inputDimension outputDimension coefficient
  change ‖coefficient.1‖ = _
  have oneToReal : (1 : ℝ≥0∞).toReal = 1 := by norm_num
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  rw [oneToReal]
  simp only [Real.rpow_one, weightedDerivative]
  rw [show (1 / (1 : ℝ)) = 1 by norm_num, Real.rpow_one]
  have summable : Summable (fun pair : ℤ × DerivativeIndex grade => ‖coefficient.1 pair‖) := by
    simpa only [oneToReal, Real.rpow_one] using
      (lp.memℓp coefficient.1).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  rw [summable.tsum_prod]
  simp only [tsum_fintype]

theorem weighted_derivative_literal : LiteralDerivativeGoal L sigma gamma ell := by
  intro grade inputDimension outputDimension coefficient cell index point
  change coefficient.1 (cell, index) point =
    (coefficientScale L sigma gamma ell grade cell index point : ℂ) •
      ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹ •
        coefficient.1 (cell, index) point)
  rw [← mul_smul]
  have nonzero : (coefficientScale L sigma gamma ell grade cell index point : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (coefficientScale_pos L sigma gamma ell grade cell index point).ne'
  rw [mul_inv_cancel₀ nonzero, one_smul]

end Grad.GaugeCoefficients.Algebra
