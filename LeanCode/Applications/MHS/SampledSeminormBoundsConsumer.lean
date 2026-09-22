import SampledSeminormBounds

noncomputable section

open Set

namespace Grad.PhysicalFamily.SampledSeminormBounds.Consumer

open Grad.MainTarget
open Grad.PhysicalFamily
open Grad.PhysicalFamily.SampledSeminormBounds

theorem remainder_value_norm_le_physicalBound
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1)
    (time : ℝ) (timeIn : time ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    ‖family.remainder epsilon parameter.val point time‖ ≤
      family.bound * |epsilon| := by
  simpa using
    (remainder_iteratedFDeriv_le_physicalBound cellLength family epsilon
      epsilonIn parameter 0 point pointIn time timeIn)

theorem tilt_value_norm_le_physicalBound
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (time : ℝ) (timeIn : time ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    ‖family.tilt epsilon parameter.val time‖ ≤ family.bound * |epsilon| := by
  simpa using
    (tilt_iteratedFDeriv_le_physicalBound cellLength family epsilon epsilonIn
      parameter 0 time timeIn)

theorem remainder_fderiv_norm_le_physicalBound
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1)
    (time : ℝ) (timeIn : time ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    ‖fderiv ℝ
      (fun argument : Vec => family.remainder epsilon parameter.val
        (coordinateDisk argument) (argument 1))
      (coordinatePoint point time)‖ ≤ family.bound * |epsilon| := by
  simpa [norm_iteratedFDeriv_one] using
    (remainder_iteratedFDeriv_le_physicalBound cellLength family epsilon
      epsilonIn parameter 1 point pointIn time timeIn)

theorem tilt_fderiv_norm_le_physicalBound
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (time : ℝ) (timeIn : time ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    ‖fderiv ℝ (family.tilt epsilon parameter.val) time‖ ≤
      family.bound * |epsilon| := by
  simpa [norm_iteratedFDeriv_one] using
    (tilt_iteratedFDeriv_le_physicalBound cellLength family epsilon epsilonIn
      parameter 1 time timeIn)

end Grad.PhysicalFamily.SampledSeminormBounds.Consumer
