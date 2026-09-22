import AHQ14OriginalSevenSlotContinuity
import AHR2OriginalSevenSlotOneHigh
import SCC30OriginalRowCoordinates

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift

/-- Exact quotient of the original bulk weights. The common sqrt(r)
factor cancels; no boundary half-order is inserted. -/
def bulkWeightRatio (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (shift mode : ℤ × ℤ) : ℝ :=
  Real.exp (radialPhase parameters radius mode.2 -
    radialPhase parameters radius (twoFrequencyTranslation shift mode).2) *
    annularFrequency mode.1 mode.2 ^ power /
      annularFrequency (twoFrequencyTranslation shift mode).1
        (twoFrequencyTranslation shift mode).2 ^ power

theorem bulkWeightRatio_pos (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (shift mode : ℤ × ℤ) :
    0 < bulkWeightRatio parameters power radius shift mode := by
  unfold bulkWeightRatio
  exact div_pos (mul_pos (Real.exp_pos _) (pow_pos (annularFrequency_pos mode) _))
    (pow_pos (annularFrequency_pos (twoFrequencyTranslation shift mode)) _)

theorem bulkWeightRatio_continuous (parameters : PhaseParameters) (power : ℕ)
    (shift mode : ℤ × ℤ) :
    Continuous (fun radius => bulkWeightRatio parameters power radius shift mode) := by
  unfold bulkWeightRatio radialPhase
  fun_prop

theorem bulkFrequency_shift_le (mode shift : ℤ × ℤ) :
    annularFrequency mode.1 mode.2 ≤ annularFrequency shift.1 shift.2 *
      annularFrequency (twoFrequencyTranslation shift mode).1
        (twoFrequencyTranslation shift mode).2 := by
  have result := annularFrequency_sub_le_mul (twoFrequencyTranslation shift mode) (-shift)
  simpa [twoFrequencyTranslation, annularFrequency, mul_comm] using result

theorem bulkPhase_ratio_le (parameters : PhaseParameters) (r : RadialPoint)
    (shift mode : ℤ × ℤ) :
    Real.exp (radialPhase parameters r.val mode.2 -
      radialPhase parameters r.val (twoFrequencyTranslation shift mode).2) ≤
      boundaryCoefficientPhaseCost (radialKernelParameters parameters r) shift := by
  have phase := (exp_radialPhase_ratio parameters r.val r.property.1 r.property.2
    mode.2 (twoFrequencyTranslation shift mode).2).trans
    (exp_radialPhase_le parameters r.val r.property.1 r.property.2
      (mode.2 - (twoFrequencyTranslation shift mode).2))
  have difference : mode.2 - (twoFrequencyTranslation shift mode).2 = shift.2 := by simp
  rw [difference] at phase
  apply phase.trans
  rw [radialKernelPhaseCost]
  change Real.exp (parameters.sigma0 + parameters.gamma) *
    coefficientRadialEnvelope parameters shift.2 r.val ≤ _
  apply mul_le_mul_of_nonneg_right _ (by unfold coefficientRadialEnvelope; positivity)
  apply Real.exp_le_exp.mpr
  have bound := mul_nonneg parameters.gamma_pos.le (sub_nonneg.mpr r.property.2)
  nlinarith

theorem bulkWeightRatio_le (parameters : PhaseParameters) (power : ℕ)
    (r : RadialPoint) (shift mode : ℤ × ℤ) :
    bulkWeightRatio parameters power r.val shift mode ≤
      boundaryCoefficientPhaseCost (radialKernelParameters parameters r) shift *
        annularFrequency shift.1 shift.2 ^ power := by
  rw [bulkWeightRatio, div_le_iff₀
    (pow_pos (annularFrequency_pos (twoFrequencyTranslation shift mode)) power)]
  have frequency := pow_le_pow_left₀ (annularFrequency_pos mode).le
    (bulkFrequency_shift_le mode shift) power
  rw [mul_pow] at frequency
  exact (mul_le_mul (bulkPhase_ratio_le parameters r shift mode) frequency
    (pow_nonneg (annularFrequency_pos mode).le power)
    (boundaryCoefficientPhaseCost_nonnegative _ _)).trans_eq (mul_assoc _ _ _).symm

theorem bulkWeightRatio_original (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (positive : 0 < radius) (shift mode : ℤ × ℤ) :
    bulkWeightRatio parameters power radius shift mode =
      originalRowWeight parameters power radius mode /
        originalRowWeight parameters power radius (twoFrequencyTranslation shift mode) := by
  unfold bulkWeightRatio originalRowWeight
  rw [Real.exp_sub]
  field_simp

end Grad.AnnularKernelL2
