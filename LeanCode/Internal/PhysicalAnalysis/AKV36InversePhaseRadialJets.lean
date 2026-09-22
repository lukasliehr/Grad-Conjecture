import AKH3ExactPhaseDiagonalCoefficient
import AW3Exponential

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.PhaseAlgebra Grad.AnnularVariational
open Grad.AnalyticWeights.Calculus Grad.AnalyticWeights.Higher Grad.AnnularWeightedSmoothness

def inversePhaseCurve (parameters : PhaseParameters) (cell : ℤ) (radius : ℝ) : ℝ :=
  Real.exp (-radialPhase parameters radius cell)

theorem inversePhaseCurve_smooth (parameters : PhaseParameters) (cell : ℤ) :
    ContDiff ℝ ∞ (inversePhaseCurve parameters cell) :=
  Real.contDiff_exp.comp ((Grad.AnnularWeightedSmoothness.radialPhase_smooth parameters cell).neg)

theorem inversePhaseCurve_ray (parameters : PhaseParameters) (cell : ℤ) :
    inversePhaseCurve parameters cell =
      inverseWeight parameters.sigma0 parameters.gamma 1 cell ∘ phaseRadialRay := by
  funext radius
  rw [Function.comp_apply,inverseWeight_exp]
  change Real.exp (-radialPhase parameters radius cell) =
    Real.exp (-cartesianPhase parameters cell (phaseRadialRay radius))
  rw [congrFun (radialPhase_ray parameters cell) radius]
  rfl

theorem inversePhaseCurve_le_one (parameters : PhaseParameters) (cell : ℤ)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    inversePhaseCurve parameters cell radius ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  apply neg_nonpos.mpr
  rw [radialPhase_decompose]
  exact add_nonneg
    (mul_nonneg (phaseWidth_nonneg parameters radius nonnegative bounded) (cellFrequency_pos cell).le)
    (mul_nonneg parameters.gamma_pos.le (concaveGap_nonneg _ (mul_nonneg nonnegative (cellFrequency_pos cell).le)))

def inversePhaseJetConstant (parameters : PhaseParameters) (rank : ℕ) : ℝ :=
  if rank = 0 then 1 else partitionProductConstant rank * weightCost rank parameters.gamma 1

theorem inversePhaseJetConstant_nonnegative (parameters : PhaseParameters) (rank : ℕ) :
    0 ≤ inversePhaseJetConstant parameters rank := by
  have gamma := parameters.gamma_pos.le
  unfold inversePhaseJetConstant weightCost
  split_ifs
  · norm_num
  · exact mul_nonneg (partitionProductConstant_nonnegative _) (by positivity)

theorem inversePhaseCurve_iterated_bound (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (rank : ℕ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    ‖iteratedDeriv rank (inversePhaseCurve parameters mode.2) radius‖ ≤
      inversePhaseJetConstant parameters rank * annularFrequency mode.1 mode.2 ^ rank := by
  by_cases zero : rank = 0
  · subst rank
    simpa [inversePhaseJetConstant,inversePhaseCurve,Real.norm_of_nonneg (Real.exp_pos _).le] using
      inversePhaseCurve_le_one parameters mode.2 radius nonnegative bounded
  have smooth : ContDiff ℝ ∞ (inverseWeight parameters.sigma0 parameters.gamma 1 mode.2) := by
    have same : inverseWeight parameters.sigma0 parameters.gamma 1 mode.2 =
        fun point => Real.exp (-physicalPhase parameters.sigma0 parameters.gamma 1 mode.2 point) :=
      funext (inverseWeight_exp _ _ _ _)
    rw [same]
    exact Real.contDiff_exp.comp ((physicalPhase_contDiff _ _ _ _).neg)
  have derivativeBound := inverseWeight_iterated_norm_bound parameters.sigma0 parameters.gamma 1 mode.2
    parameters.gamma_pos.le (by norm_num) rank (by omega) (phaseRadialRay radius)
  have rayBound := radialRay_iteratedDeriv_bound _ smooth rank radius
  rw [← inversePhaseCurve_ray] at rayBound
  have frequencyBound : Grad.CellWeights.cellWeight mode.2 ≤ annularFrequency mode.1 mode.2 := by
    apply (cellFrequency_le_polynomial mode.2).trans
    change 1 + |(mode.2 : ℝ)| ≤ 1 + |(mode.1 : ℝ)| + |(mode.2 : ℝ)|
    linarith [abs_nonneg (mode.1 : ℝ)]
  have weightSame : inverseWeight parameters.sigma0 parameters.gamma 1 mode.2 (phaseRadialRay radius) =
      inversePhaseCurve parameters mode.2 radius := congrFun (inversePhaseCurve_ray parameters mode.2) radius |>.symm
  rw [weightSame] at derivativeBound
  apply (rayBound.trans derivativeBound).trans
  rw [inversePhaseJetConstant,if_neg zero]
  have constantNonnegative : 0 ≤ partitionProductConstant rank * weightCost rank parameters.gamma 1 := by
    simpa [inversePhaseJetConstant,zero] using inversePhaseJetConstant_nonnegative parameters rank
  apply mul_le_mul
  · exact mul_le_of_le_one_right constantNonnegative
      (inversePhaseCurve_le_one parameters mode.2 radius nonnegative bounded)
  · exact pow_le_pow_left₀ (Grad.CellWeights.cellWeight_pos _).le frequencyBound _
  · exact pow_nonneg (Grad.CellWeights.cellWeight_pos _).le _
  · have h := inversePhaseJetConstant_nonnegative parameters rank
    simpa [inversePhaseJetConstant,zero] using h

end Grad.AnnularGeneralSourceRegularity
