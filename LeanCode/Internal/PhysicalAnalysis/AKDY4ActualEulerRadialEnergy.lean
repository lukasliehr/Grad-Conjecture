import AKDY3FiniteEulerRadialEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
open Set Filter MeasureTheory
open scoped ENNReal ContDiff
namespace Grad.OriginalRadialRecovery
open Grad.OriginalCartesianTameEstimate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem rawEulerPolynomial_continuousOn (domain : Set ℝ) (jets : ℕ → ℝ → E)
    (continuous : ∀ rank,ContinuousOn (jets rank) domain) (terms : List (ℕ × ℝ)) :
    ContinuousOn (rawEulerPolynomial jets terms) domain := by
  induction terms with
  | nil => exact continuousOn_const
  | cons term terms previous =>
      exact ((((continuousOn_id.pow (term.1+1)).smul (continuous (term.1+1))).const_smul term.2)).add previous

theorem actualRawEulerJets_continuousOn (domain : Set ℝ) (jets : ℕ → ℝ → E)
    (continuous : ∀ rank,ContinuousOn (jets rank) domain) (rank : ℕ) :
    ContinuousOn (actualRawEulerJets jets rank) domain := by
  cases rank with
  | zero => exact continuous 0
  | succ rank => exact rawEulerPolynomial_continuousOn domain jets continuous (positiveEulerTerms rank)

/-- Actual Euler energy controls actual ordinary radial derivative energy
for the identical smooth curve on the full original closed collar. All
constants depend only on its fixed lower radius and the requested rank. -/
theorem actualEuler_radial_squareEnergy (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (curve : ℝ → E) (smooth : ContDiffOn ℝ ∞ curve (Icc lower 1))
    (rank : ℕ) (payment : ℝ) (paymentNonnegative : 0≤payment)
    (energy : ∀ order,order≤rank →
      (∫⁻ radius in Icc lower 1,ENNReal.ofReal
        (‖vectorEulerWithinIteratedDerivative (Icc lower 1) order curve radius‖^2))≤ENNReal.ofReal (payment^2)) :
    (∫⁻ radius in Icc lower 1,ENNReal.ofReal
      (‖iteratedDerivWithin rank curve (Icc lower 1) radius‖^2))≤
      ENNReal.ofReal ((rawRadialEnergyConstant lower rank*payment)^2) := by
  let raw := fun order => iteratedDerivWithin order curve (Icc lower 1)
  have rawContinuous (order : ℕ) : ContinuousOn (raw order) (Icc lower 1) :=
    smooth.continuousOn_iteratedDerivWithin
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl order) (uniqueDiffOn_Icc bounded)
  have rawDerivative (order : ℕ) (radius : ℝ) (inside : radius∈Icc lower 1) :
      HasDerivWithinAt (raw order) (raw (order+1) radius) (Icc lower 1) radius := by
    dsimp only [raw]
    rw [iteratedDerivWithin_succ]
    exact (smooth.differentiableOn_iteratedDerivWithin
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl order)
      (uniqueDiffOn_Icc bounded) radius inside).hasDerivWithinAt
  let jets := actualRawEulerJets raw
  have continuous (order : ℕ) : ContinuousOn (jets order) (Icc lower 1) :=
    actualRawEulerJets_continuousOn (Icc lower 1) raw rawContinuous order
  have derivative (order : ℕ) (radius : ℝ) (inside : radius∈Icc lower 1) :
      HasDerivWithinAt (jets order) (radius⁻¹ • jets (order+1) radius) (Icc lower 1) radius :=
    actualRawEulerJets_hasDerivWithinAt (Icc lower 1) raw radius (positive.trans_le inside.1).ne'
      (fun raw => rawDerivative raw radius inside) order
  have paid (order : ℕ) (orderLe : order≤rank) :
      (∫⁻ radius in Icc lower 1,ENNReal.ofReal (‖jets order radius‖^2))≤ENNReal.ofReal (payment^2) := by
    have fidelity := actualRawEulerJets_fidelity (Icc lower 1) (uniqueDiffOn_Icc bounded)
      (fun radius inside => (positive.trans_le inside.1).ne') raw rawDerivative order
    have identity :
        (∫⁻ radius in Icc lower 1,ENNReal.ofReal (‖jets order radius‖^2))=
        ∫⁻ radius in Icc lower 1,ENNReal.ofReal
          (‖vectorEulerWithinIteratedDerivative (Icc lower 1) order curve radius‖^2) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
      exact congrArg (fun value : E => ENNReal.ofReal (‖value‖^2)) (fidelity inside).symm
    rw [identity]
    exact energy order orderLe
  exact radialTower_squareEnergy lower positive bounded jets continuous derivative rank payment paymentNonnegative paid

end Grad.OriginalRadialRecovery
