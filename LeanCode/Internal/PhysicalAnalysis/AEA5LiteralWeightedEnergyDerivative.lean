import AEA4FullReferenceDissipation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowReference
open Grad.AnnularLowEnergy Grad.AnnularVariational Grad.PhaseAlgebra
open Grad.CartesianState

/-- Literal rho(r) mu_n(r)^-1, the BE18 half-order energy density. -/
def lowEnergyDensity (length radius : ℝ) (cell : ℤ) : ℝ :=
  radius ^ (-(7 / 2 : ℝ)) * (lowMu length radius cell)⁻¹

theorem lowEnergyDensity_pos (length radius : ℝ) (cell : ℤ) (positive : 0 < radius) :
    0 < lowEnergyDensity length radius cell :=
  mul_pos (Real.rpow_pos_of_pos positive _) (inv_pos.mpr (lowMu_pos length radius cell positive))

theorem lowEnergyDensity_mu (length radius : ℝ) (cell : ℤ) (positive : 0 < radius) :
    lowEnergyDensity length radius cell * lowMu length radius cell = radius ^ (-(7 / 2 : ℝ)) := by
  rw [lowEnergyDensity, mul_assoc, inv_mul_cancel₀ (lowMu_pos length radius cell positive).ne', mul_one]

theorem lowEnergyDensity_hasDerivAt (length radius : ℝ) (cell : ℤ) (positive : 0 < radius) :
    HasDerivAt (fun point => lowEnergyDensity length point cell)
      (lowEnergyDensity length radius cell * (-(7 / 2 : ℝ) / radius - lowMuLogSlope length radius cell)) radius := by
  have weight := Real.hasDerivAt_rpow_const (x := radius) (p := -(7 / 2 : ℝ)) (Or.inl positive.ne')
  have inverse := lowMuInverse_hasDerivAt length radius cell positive
  have equality : lowEnergyDensity length radius cell * (-(7 / 2 : ℝ) / radius - lowMuLogSlope length radius cell) =
      (-(7 / 2 : ℝ) * radius ^ (-(7 / 2 : ℝ) - 1)) * (lowMu length radius cell)⁻¹ +
        radius ^ (-(7 / 2 : ℝ)) * (-(lowMuLogSlope length radius cell) / lowMu length radius cell) := by
    rw [Real.rpow_sub positive, Real.rpow_one]
    unfold lowEnergyDensity
    ring
  rw [equality]
  exact weight.mul inverse

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def lowPairEnergy (length radius : ℝ) (mode : LowAnnularMode) (first second : E) : ℝ :=
  lowEnergyDensity length radius mode.val.2 * (‖first‖ ^ 2 + ‖second‖ ^ 2)

def lowPairEnergySlope (parameters : PhaseParameters) (length radius : ℝ) (mode : LowAnnularMode)
    (first second forcingFirst forcingSecond : E) : ℝ :=
  lowEnergyDensity length radius mode.val.2 *
    ((-(7 / 2 : ℝ) / radius - lowMuLogSlope length radius mode.val.2) * (‖first‖ ^ 2 + ‖second‖ ^ 2) +
      2 * inner ℝ first (lowReferenceFirst parameters length radius mode first second + lowMu length radius mode.val.2 • forcingFirst) +
      2 * inner ℝ second (lowReferenceSecond parameters length radius mode first second + lowMu length radius mode.val.2 • forcingSecond))

/-- Actual differentiation of the original weighted energy along the exact
reference equation; the derivative of mu is included once and only once. -/
theorem lowPairEnergy_hasDerivAt (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) (positive : 0 < radius) (first second : ℝ → E) (forcingFirst forcingSecond : E)
    (firstDerivative : HasDerivAt first
      (lowReferenceFirst parameters length radius mode (first radius) (second radius) + lowMu length radius mode.val.2 • forcingFirst) radius)
    (secondDerivative : HasDerivAt second
      (lowReferenceSecond parameters length radius mode (first radius) (second radius) + lowMu length radius mode.val.2 • forcingSecond) radius) :
    HasDerivAt (fun point => lowPairEnergy length point mode (first point) (second point))
      (lowPairEnergySlope parameters length radius mode (first radius) (second radius) forcingFirst forcingSecond) radius := by
  have energy := (lowEnergyDensity_hasDerivAt length radius mode.val.2 positive).mul
    (firstDerivative.norm_sq.add secondDerivative.norm_sq)
  have equality : lowPairEnergySlope parameters length radius mode (first radius) (second radius) forcingFirst forcingSecond =
      (lowEnergyDensity length radius mode.val.2 * (-(7 / 2 : ℝ) / radius - lowMuLogSlope length radius mode.val.2)) *
          (‖first radius‖ ^ 2 + ‖second radius‖ ^ 2) +
        lowEnergyDensity length radius mode.val.2 *
          (2 * inner ℝ (first radius) (lowReferenceFirst parameters length radius mode (first radius) (second radius) +
            lowMu length radius mode.val.2 • forcingFirst) +
          2 * inner ℝ (second radius) (lowReferenceSecond parameters length radius mode (first radius) (second radius) +
            lowMu length radius mode.val.2 • forcingSecond)) := by
    unfold lowPairEnergySlope
    ring
  rw [equality]
  exact energy

/-- Forcing is exactly mu F in the equation, hence F in the weighted energy. -/
theorem lowPairEnergySlope_forcing (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) (positive : 0 < radius) (first second forcingFirst forcingSecond : E) :
    lowPairEnergySlope parameters length radius mode first second forcingFirst forcingSecond =
      radius ^ (-(7 / 2 : ℝ)) * ((lowMu length radius mode.val.2)⁻¹ *
        ((-(7 / 2 : ℝ) / radius - lowMuLogSlope length radius mode.val.2) * (‖first‖ ^ 2 + ‖second‖ ^ 2) +
          2 * inner ℝ first (lowReferenceFirst parameters length radius mode first second) +
          2 * inner ℝ second (lowReferenceSecond parameters length radius mode first second))) +
      2 * radius ^ (-(7 / 2 : ℝ)) * (inner ℝ first forcingFirst + inner ℝ second forcingSecond) := by
  simp only [lowPairEnergySlope, inner_add_right, inner_smul_right]
  unfold lowEnergyDensity
  field_simp [(lowMu_pos length radius mode.val.2 positive).ne']
  ring

end Hilbert
end Grad.AnnularLowReference
