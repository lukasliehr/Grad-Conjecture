import ANG9GradientSymmetry
import ANH18WeakSolve

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.CircularHighWeak
open Grad.CartesianState

theorem highMass_angular_symmetric (mode : ℤ) (first second : highDiskGrade) :
    inner ℂ (diskB (highDiskBulk (highDiskMode mode first))) (highDiskBulk second) =
      inner ℂ (diskB (highDiskBulk first)) (highDiskBulk (highDiskMode mode second)) := by
  have projected := (congrArg diskB (highDiskMode_bulk mode first)).trans
    (diskB_angular_commute mode (highDiskBulk first))
  exact (congrArg (fun value : DiskL2 1 => inner ℂ value (highDiskBulk second)) projected).trans
    ((diskMode_symmetric mode (diskB (highDiskBulk first)) (highDiskBulk second)).trans
      (congrArg (fun value : DiskL2 1 => inner ℂ (diskB (highDiskBulk first)) value)
        (highDiskMode_bulk mode second).symm))

/-- The actual completed Robin bilinear form commutes with every angular mode. -/
theorem robinForm_angular (parameter : ℝ) (mode : ℤ) (field test : highDiskGrade) :
    robinForm parameter (highDiskMode mode field) test =
      robinForm parameter field (highDiskMode mode test) := by
  refine (robinForm_apply parameter (highDiskMode mode field) test).trans
    (Eq.trans ?_ (robinForm_apply parameter field (highDiskMode mode test)).symm)
  change (inner ℂ (highGradX (highDiskMode mode field)) (highGradX test)).re +
      (inner ℂ (highGradY (highDiskMode mode field)) (highGradY test)).re +
      parameter ^ 2 * (inner ℂ (diskB (highDiskBulk (highDiskMode mode field))) (highDiskBulk test)).re +
      2 * (inner ℂ (robinTrace (highDiskMode mode field)) (robinTrace test)).re =
    (inner ℂ (highGradX field) (highGradX (highDiskMode mode test))).re +
      (inner ℂ (highGradY field) (highGradY (highDiskMode mode test))).re +
      parameter ^ 2 * (inner ℂ (diskB (highDiskBulk field)) (highDiskBulk (highDiskMode mode test))).re +
      2 * (inner ℂ (robinTrace field) (robinTrace (highDiskMode mode test))).re
  exact congrArg₂ (fun first second : ℝ => first + second)
    (congrArg₂ (fun first second : ℝ => first + second)
      (highGradient_angular_symmetric mode field test)
      (congrArg (fun value : ℂ => parameter ^ 2 * value.re) (highMass_angular_symmetric mode field test)))
    (congrArg (fun value : ℂ => 2 * value.re) (robinTrace_angular_symmetric mode field test))

private theorem robinValue_test_smul (parameter : ℝ) (scalar : ℂ) (field test : highDiskGrade) :
    robinValue parameter field (scalar • test) = starRingEnd ℂ scalar * robinValue parameter field test := by
  simp only [robinValue, map_smul, inner_smul_left]
  ring

/-- Exact complex AN18 form commutation, with its original trace and multiplier. -/
theorem robinValue_angular (parameter : ℝ) (mode : ℤ) (field test : highDiskGrade) :
    robinValue parameter (highDiskMode mode field) test =
      robinValue parameter field (highDiskMode mode test) := by
  have realPart (probe : highDiskGrade) :
      (robinValue parameter (highDiskMode mode field) probe).re =
        (robinValue parameter field (highDiskMode mode probe)).re :=
    (robinForm_literal parameter (highDiskMode mode field) probe).symm.trans
      ((robinForm_angular parameter mode field probe).trans
        (robinForm_literal parameter field (highDiskMode mode probe)))
  have imaginary := realPart (Complex.I • test)
  have mapped := (highDiskMode mode).map_smul Complex.I test
  have right := (congrArg (fun value : highDiskGrade => robinValue parameter field value) mapped).trans
    (robinValue_test_smul parameter Complex.I field (highDiskMode mode test))
  have left := robinValue_test_smul parameter Complex.I (highDiskMode mode field) test
  have imaginaryPair := (congrArg Complex.re left).symm.trans
    (imaginary.trans (congrArg Complex.re right))
  have character (value : ℂ) : (starRingEnd ℂ Complex.I * value).re = value.im := by simp
  exact Complex.ext (realPart test)
    ((character _).symm.trans (imaginaryPair.trans (character _)))

/-- The constructed high Robin weak inverse commutes with the genuine
completed angular projections on both its L2 source and H1 solution. -/
theorem highRobinWeakInverse_angular (parameter : ℝ) (mode : ℤ) (source : highDiskL2) :
    highDiskMode mode (highRobinWeakInverse parameter source) =
      highRobinWeakInverse parameter (highL2Mode mode source) := by
  apply weakSolution_unique parameter (highL2Mode mode source)
  intro test
  have equation := (robinValue_angular parameter mode (highRobinWeakInverse parameter source) test).trans
    (highRobinWeakInverse_equation parameter source (highDiskMode mode test))
  refine equation.trans ?_
  exact (congrArg (fun value : DiskL2 1 => inner ℂ value source.val) (highDiskMode_bulk mode test)).trans
    (diskMode_symmetric mode (highDiskBulk test) source.val)

end Grad.CircularHighWeak
