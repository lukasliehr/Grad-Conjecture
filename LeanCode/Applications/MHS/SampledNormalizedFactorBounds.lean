import SampledSeminormBoundsConsumer

noncomputable section

open Set

namespace Grad.PhysicalFamily.SampledNormalizedFactorBounds

open Grad.MainTarget
open Grad.PhysicalFamily
open Grad.PhysicalFamily.SampledSeminormBounds.Consumer

theorem normalizedFactor_sq_of_tiltBound (tilt : Plane)
    (tiltBound : ‖tilt‖ ^ 2 < 2) :
    normalizedFactor tilt ^ 2 = 1 - ‖tilt‖ ^ 2 / 2 := by
  unfold normalizedFactor
  rw [Real.sq_sqrt]
  nlinarith [sq_nonneg ‖tilt‖]

theorem normalizedFactor_nonnegative (tilt : Plane) :
    0 ≤ normalizedFactor tilt :=
  Real.sqrt_nonneg _

theorem normalizedFactor_le_one (tilt : Plane)
    (_tiltBound : ‖tilt‖ ^ 2 < 2) :
    normalizedFactor tilt ≤ 1 := by
  rw [normalizedFactor, Real.sqrt_le_one]
  nlinarith [sq_nonneg ‖tilt‖]

theorem abs_normalizedFactor_sub_one_le (tilt : Plane)
    (tiltBound : ‖tilt‖ ^ 2 < 2) :
    |normalizedFactor tilt - 1| ≤ ‖tilt‖ ^ 2 / 2 := by
  have factorNonnegative := normalizedFactor_nonnegative tilt
  have factorLe := normalizedFactor_le_one tilt tiltBound
  have factorSq := normalizedFactor_sq_of_tiltBound tilt tiltBound
  rw [abs_of_nonpos (sub_nonpos.mpr factorLe)]
  have productNonnegative :
      0 ≤ normalizedFactor tilt * (1 - normalizedFactor tilt) :=
    mul_nonneg factorNonnegative (sub_nonneg.mpr factorLe)
  nlinarith

theorem sampled_abs_normalizedFactor_sub_one_le
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (time : ℝ) (timeIn : time ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    |normalizedFactor (family.tilt epsilon parameter.val time) - 1| ≤
      (family.bound * |epsilon|) ^ 2 / 2 := by
  have tiltBound := family.tiltBound epsilon epsilonIn parameter.val
    parameter.property time
  have normBound := tilt_value_norm_le_physicalBound cellLength family epsilon
    epsilonIn parameter time timeIn
  have errorNonnegative : 0 ≤ family.bound * |epsilon| :=
    mul_nonneg (le_trans zero_le_one family.boundAtLeastOne) (abs_nonneg _)
  have squareBound :
      ‖family.tilt epsilon parameter.val time‖ ^ 2 ≤
        (family.bound * |epsilon|) ^ 2 := by
    exact sq_le_sq₀ (norm_nonneg _) errorNonnegative |>.mpr normBound
  exact (abs_normalizedFactor_sub_one_le _ tiltBound).trans
    (div_le_div_of_nonneg_right squareBound (by norm_num))

end Grad.PhysicalFamily.SampledNormalizedFactorBounds
