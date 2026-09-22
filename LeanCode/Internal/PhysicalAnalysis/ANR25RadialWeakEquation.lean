import ANR24LaplacianTestL2

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.NonlinearDivision

theorem collar_supported_inside (lower : ℝ) (positive : 0 < lower) (test : ℝ → ℝ)
    (supported : tsupport test ⊆ Ioo lower 1) : tsupport test ⊆ Ioo (0 : ℝ) 1 := by
  intro radius member
  exact ⟨positive.trans (supported member).1, (supported member).2⟩

/-- The actual AN18 inverse satisfies the compact radial distributional
Laplacian equation on every positive closed collar. Only the test is smooth. -/
theorem weakInverse_radial_secondTest (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameter : ℝ) (source : highDiskL2) (mode : ℤ) (vector : ComplexEuclidean 1)
    (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test) (supported : tsupport test ⊆ Ioo lower 1) :
    radialPairing lower positive (fun radius => radius * radialTestOperator mode test radius)
      (continuous_id.mul (radialTestOperator_smooth mode test smooth (collar_supported_inside lower positive test supported)).continuous)
      vector (diskL2Radial lower positive bounded mode (highDiskBulk (highRobinWeakInverse parameter source))) =
    radialPairing lower positive (fun radius => radius * test radius) (continuous_id.mul smooth.continuous)
      vector (diskL2Radial lower positive bounded mode (weakLaplacianValue parameter source)) := by
  let inside := collar_supported_inside lower positive test supported
  let operatorSmooth := radialTestOperator_smooth mode test smooth inside
  let operatorInside := (radialTestOperator_support mode test).trans inside
  let operatorSupport := (radialTestOperator_support mode test).trans supported
  let bulk := highDiskBulk (highRobinWeakInverse parameter source)
  have equation := weakInverse_compact parameter source (radialTestLift mode vector test)
    (radialTestLift_smooth mode vector test smooth inside)
    (radialTestLift_compact mode vector test inside) (radialTestLift_inside mode vector test inside)
  have replacement := congrArg (fun value : DiskL2 1 => inner ℂ value bulk)
    (radialTestJet_laplacianL2 mode vector test smooth inside)
  have left := radialTestJet_pairing lower positive bounded mode vector (radialTestOperator mode test)
    operatorSmooth operatorInside operatorSupport bulk
  have right := radialTestJet_pairing lower positive bounded mode vector test smooth inside supported
    (weakLaplacianValue parameter source)
  have normalized := left.symm.trans (replacement.symm.trans (equation.trans right))
  apply smul_right_injective ℂ (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  dsimp only
  exact normalized

/-- The radial forcing is exactly k²(1−4/m²)z_m−F_m, with the same
actual inverse coefficient and the same actual source coefficient. -/
theorem weakInverse_radial_rhs (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameter : ℝ) (source : highDiskL2) (mode : ℤ) (high : mode ∉ lowAngularModes) :
    diskL2Radial lower positive bounded mode (weakLaplacianValue parameter source) =
      (((parameter ^ 2 * (1 - 4 / (mode : ℝ) ^ 2) : ℝ)) : ℂ) •
        diskL2Radial lower positive bounded mode (highDiskBulk (highRobinWeakInverse parameter source)) -
      diskL2Radial lower positive bounded mode source.val := by
  change diskL2Radial lower positive bounded mode
    (((parameter ^ 2 : ℝ) : ℂ) • diskB (highDiskBulk (highRobinWeakInverse parameter source)) - source.val) = _
  let radial : DiskL2 1 →L[ℂ] RadialL2 1 lower := diskL2Radial lower positive bounded mode
  let bulk : DiskL2 1 := highDiskBulk (highRobinWeakInverse parameter source)
  let scalar : ℂ := ((parameter ^ 2 : ℝ) : ℂ)
  let multiplier : ℂ := ((1 - 4 / (mode : ℝ) ^ 2 : ℝ) : ℂ)
  have multiply : radial (scalar • diskB bulk) = (scalar * multiplier) • radial bulk :=
    (radial.map_smul scalar (diskB bulk)).trans
      ((congrArg (fun value : RadialL2 1 lower => scalar • value)
        (diskL2Radial_B lower positive bounded mode high bulk)).trans
        (smul_smul scalar multiplier (radial bulk)))
  have subtract := radial.map_sub (scalar • diskB bulk) source.val
  have result := subtract.trans (congrArg (fun value : RadialL2 1 lower => value - radial source.val) multiply)
  have cast : scalar * multiplier = (((parameter ^ 2 * (1 - 4 / (mode : ℝ) ^ 2) : ℝ)) : ℂ) :=
    (Complex.ofReal_mul _ _).symm
  exact result.trans (congrArg (fun value : ℂ => value • radial bulk - radial source.val) cast)

end Grad.CircularHighRegularity
