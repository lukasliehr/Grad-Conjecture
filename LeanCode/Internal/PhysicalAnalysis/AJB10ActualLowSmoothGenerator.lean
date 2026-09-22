import AJB9ActualLowMixedJetDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal ContDiff
namespace Grad.AnnularLowOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularKernelOrbit
open Grad.AnnularKernelL2 Grad.AnnularKernelContinuity Grad.BoundaryKernelAction Grad.AnnularReconstruction

section SmoothTower
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
/-- Actual completed derivative columns at every order give smoothness in the
complete norm, rather than only coefficientwise smoothness. -/
theorem orbitJetTower_contDiff_nat (jet : ℕ → ℕ → OrbitParameter → E)
    (derivative : ∀ angular cell tau, HasFDerivAt (jet angular cell)
      (orbitDifferential (jet (angular + 1) cell tau) (jet angular (cell + 1) tau)) tau)
    (order angular cell : ℕ) : ContDiff ℝ order (jet angular cell) := by
  induction order generalizing angular cell with
  | zero =>
    change ContDiff ℝ (0 : WithTop ℕ∞) (jet angular cell)
    rw [contDiff_zero]
    exact continuous_iff_continuousAt.mpr (fun tau => (derivative angular cell tau).continuousAt)
  | succ order induction =>
    rw [show (order.succ : WithTop ℕ∞) = (order : WithTop ℕ∞) + 1 by norm_num]
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun tau => orbitDifferential (jet (angular + 1) cell tau) (jet angular (cell + 1) tau), ?_, derivative angular cell⟩
    have first := ((ContinuousLinearMap.smulRightL ℝ OrbitParameter E)
      (ContinuousLinearMap.fst ℝ ℝ ℝ)).contDiff.comp (induction (angular + 1) cell)
    have second := ((ContinuousLinearMap.smulRightL ℝ OrbitParameter E)
      (ContinuousLinearMap.snd ℝ ℝ ℝ)).contDiff.comp (induction angular (cell + 1))
    exact first.add second

end SmoothTower

variable (parameters : PhaseParameters) (length compact lower : ℝ)
  (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
  (state : RetainedInverseState parameters length compact)

theorem actualLowResponseOrbitJet_contDiff (order angular cell : ℕ) :
    ContDiff ℝ order (fun tau => actualLowResponseOrbitJet parameters length compact lower lengthPositive positive bounded state tau angular cell) :=
  orbitJetTower_contDiff_nat
    (fun angular cell tau => actualLowResponseOrbitJet parameters length compact lower lengthPositive positive bounded state tau angular cell)
    (fun angular cell tau => actualLowResponseOrbitJet_hasFDerivAt parameters length compact lower lengthPositive positive bounded state tau angular cell)
    order angular cell

theorem actualLowResponseOrbitJet_zero (tau : OrbitParameter) :
    actualLowResponseOrbitJet parameters length compact lower lengthPositive positive bounded state tau 0 0 =
      actualLowResponseOrbit parameters length compact lower lengthPositive positive bounded state tau := by
  unfold actualLowResponseOrbitJet actualLowResponseOrbit actualLowRowOrbitJet actualLowRowOrbit
  rw [radialOrbitJetAction_zero, radialOrbitJetAction_zero, radialOrbitJetAction_zero]

/-- The SAME actual normalized low generator is smooth in operator norm
on the original completed bulk, without a stronger coefficient-smallness ball. -/
theorem actualLowGeneratorOrbit_contDiff (order : ℕ) :
    ContDiff ℝ order (actualLowGeneratorOrbit parameters length compact lower lengthPositive positive bounded state) := by
  have smooth := actualLowResponseOrbitJet_contDiff parameters length compact lower lengthPositive positive bounded state order 0 0
  have same : (fun tau => actualLowResponseOrbitJet parameters length compact lower lengthPositive positive bounded state tau 0 0) =
      actualLowResponseOrbit parameters length compact lower lengthPositive positive bounded state := by
    funext tau
    exact actualLowResponseOrbitJet_zero parameters length compact lower lengthPositive positive bounded state tau
  rw [same] at smooth
  exact contDiff_const.add smooth

end Grad.AnnularLowOrbit
