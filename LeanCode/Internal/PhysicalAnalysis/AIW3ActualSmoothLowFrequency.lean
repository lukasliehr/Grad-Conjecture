import AIW2ExactAJBalancing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal
namespace Grad.AnnularOriginalLow
open Grad.AnnularHighTilt Grad.AnnularLowEnergy Grad.AnnularLowReference
open Grad.AnnularVariational Grad.CartesianState Grad.PhaseAlgebra

/-- Smooth positive extension of the SAME mu; it equals mu on a neighborhood
of the entire closed collar, including both endpoints. -/
def originalLowSmoothMu (lower length : ℝ) (positive : 0 < lower) (cell : ℤ) : C(ℝ, ℝ) :=
  ⟨fun radius => lowMu length (highSmoothRadius lower radius) cell,
    Real.continuous_sqrt.comp (continuous_const.add
      (((highSmoothRadius_smooth lower).continuous.inv₀
        (fun radius => (highSmoothRadius_pos lower positive radius).ne')).pow 2))⟩

theorem originalLowSmoothMu_pos (lower length : ℝ) (positive : 0 < lower) (cell : ℤ) (radius : ℝ) :
    0 < originalLowSmoothMu lower length positive cell radius :=
  lowMu_pos length _ cell (highSmoothRadius_pos lower positive radius)

theorem originalLowSmoothMu_smooth (lower length : ℝ) (positive : 0 < lower) (cell : ℤ) :
    ContDiff ℝ ∞ (originalLowSmoothMu lower length positive cell) := by
  change ContDiff ℝ ∞ (fun radius => Real.sqrt (((cell : ℝ) / length) ^ 2 +
    (highSmoothRadius lower radius)⁻¹ ^ 2))
  apply ContDiff.sqrt
  · exact contDiff_const.add (((highSmoothRadius_smooth lower).inv
      (fun radius => (highSmoothRadius_pos lower positive radius).ne')).pow 2)
  · intro radius
    have positiveRadius := highSmoothRadius_pos lower positive radius
    positivity

def originalLowSmoothMuSlope (lower length : ℝ) (positive : 0 < lower) (cell : ℤ) : C(ℝ, ℝ) :=
  ⟨deriv (originalLowSmoothMu lower length positive cell),
    (contDiff_infty_iff_deriv.mp (originalLowSmoothMu_smooth lower length positive cell)).2.continuous⟩

theorem originalLowSmoothMu_hasDerivAt (lower length : ℝ) (positive : 0 < lower)
    (cell : ℤ) (radius : ℝ) :
    HasDerivAt (originalLowSmoothMu lower length positive cell)
      (originalLowSmoothMuSlope lower length positive cell radius) radius :=
  (originalLowSmoothMu_smooth lower length positive cell).differentiable (by simp) radius |>.hasDerivAt

theorem originalLowSmoothMu_physical (lower length : ℝ) (positive : 0 < lower)
    (cell : ℤ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    originalLowSmoothMu lower length positive cell radius = lowMu length radius cell := by
  change lowMu length (highSmoothRadius lower radius) cell = _
  rw [highSmoothRadius_eq lower positive radius (by linarith [inside.1])]

theorem originalLowSmoothMuSlope_physical (lower length : ℝ) (positive : 0 < lower)
    (cell : ℤ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    originalLowSmoothMuSlope lower length positive cell radius = lowMuSlope length radius cell := by
  change deriv (originalLowSmoothMu lower length positive cell) radius = _
  have half : lower / 2 < radius := by linarith [inside.1]
  have localEq : originalLowSmoothMu lower length positive cell =ᶠ[nhds radius]
      (fun point => lowMu length point cell) := by
    filter_upwards [Ioi_mem_nhds half] with point above
    change lowMu length (highSmoothRadius lower point) cell = _
    rw [highSmoothRadius_eq lower positive point above.le]
  rw [localEq.deriv_eq]
  exact (lowMu_hasDerivAt length radius cell (positive.trans_le inside.1)).deriv

/-- Actual w-to-v first-coordinate multiplier; the second coordinate is one.
The two phase factors are the SAME and cancel, while S_ell remains literal. -/
def originalLowRatio (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (index : LowAnnularIndex) : C(ℝ, ℝ) :=
  if index.1 = 0 then
    ⟨fun radius => originalLowScale parameters lower length index.2 /
      lowAmplitude length parameters.gamma index.2 * cellFrequency index.2.val.2 /
        originalLowSmoothMu lower length positive index.2.val.2 radius,
      continuous_const.div (originalLowSmoothMu lower length positive index.2.val.2).continuous
        (fun radius => (originalLowSmoothMu_pos lower length positive index.2.val.2 radius).ne')⟩
  else 1

theorem originalLowRatio_smooth (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (index : LowAnnularIndex) :
    ContDiff ℝ ∞ (originalLowRatio parameters lower length positive index) := by
  unfold originalLowRatio
  split_ifs
  · exact contDiff_const.div (originalLowSmoothMu_smooth lower length positive index.2.val.2)
      (fun radius => (originalLowSmoothMu_pos lower length positive index.2.val.2 radius).ne')
  · exact contDiff_const

def originalLowRatioSlope (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (index : LowAnnularIndex) : C(ℝ, ℝ) :=
  ⟨deriv (originalLowRatio parameters lower length positive index),
    (contDiff_infty_iff_deriv.mp (originalLowRatio_smooth parameters lower length positive index)).2.continuous⟩

theorem originalLowRatio_hasDerivAt (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (index : LowAnnularIndex) (radius : ℝ) :
    HasDerivAt (originalLowRatio parameters lower length positive index)
      (originalLowRatioSlope parameters lower length positive index radius) radius :=
  (originalLowRatio_smooth parameters lower length positive index).differentiable (by simp) radius |>.hasDerivAt

end Grad.AnnularOriginalLow
