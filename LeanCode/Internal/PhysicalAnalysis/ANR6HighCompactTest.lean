import ANR4CompactAngular
import ANR5CompletedGreen

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory
open scoped ContDiff

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.NonlinearQuotientBounds Grad.NonlinearDivision Grad.BoundaryTrace
open Grad.GenericCarriers

attribute [local instance] circlePeriodPositive

theorem compactBoundary_zero (test : SpatialPlane → ComplexEuclidean 1)
    (smooth : ContDiff ℝ ∞ test) (supported : tsupport test ⊆ openUnitDisk) :
    coreBoundaryL2 (globalClosedJet test smooth) = 0 := by
  have boundary : closedBoundaryValue (globalClosedJet test smooth) = 0 := by
    apply ContinuousMap.ext
    intro angle
    change test (boundaryDiskPoint angle).val = 0
    apply image_eq_zero_of_notMem_tsupport
    intro member
    have inside := supported member
    change ‖boundaryCirclePoint angle‖ < 1 at inside
    rw [boundaryCirclePoint_norm] at inside
    exact (lt_irrefl (1 : ℝ)) inside
  change (ContinuousMap.toLp 2 volume ℂ) (closedBoundaryValue (globalClosedJet test smooth)) = 0
  rw [boundary, map_zero]

/-- The right-hand side of the literal distribution equation Δz=k²Bz−F. -/
def weakLaplacianValue (parameter : ℝ) (source : highDiskL2) : DiskL2 1 :=
  ((parameter ^ 2 : ℝ) : ℂ) • diskB (highDiskBulk (highRobinWeakInverse parameter source)) - source.val

theorem weakLaplacianValue_high (parameter : ℝ) (source : highDiskL2) :
    weakLaplacianValue parameter source ∈ highDiskL2 := by
  intro mode low
  change diskMode mode (_ - _) = 0
  rw [map_sub, map_smul, diskB_coefficient,
    highDiskBulk_spectral _ mode low, source.property mode low, smul_zero, smul_zero, sub_self]

private theorem inner_smul_sub {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (test first second : V) (scalar : ℂ) :
    inner ℂ test (scalar • first - second) = scalar * inner ℂ test first - inner ℂ test second := by
  rw [inner_sub_right, inner_smul_right]

private theorem rearrangeGreen (laplacian mass forcing : ℂ)
    (equation : -laplacian + mass = forcing) : laplacian = mass - forcing := by
  linear_combination -equation

/-- AN18 implies the literal second-order equation against every smooth
compact high-sector Cartesian test, without assuming solution regularity. -/
theorem weakInverse_high_compact (parameter : ℝ) (source : highDiskL2)
    (test : SpatialPlane → ComplexEuclidean 1) (smooth : ContDiff ℝ ∞ test)
    (compact : HasCompactSupport test) (supported : tsupport test ⊆ openUnitDisk)
    (high : excludedAngularJet lowAngularModes (globalClosedJet test smooth) = globalClosedJet test smooth) :
    inner ℂ (closedL2Core (laplacianJet (globalClosedJet test smooth)))
        (highDiskBulk (highRobinWeakInverse parameter source)) =
      inner ℂ (closedL2Core (globalClosedJet test smooth)) (weakLaplacianValue parameter source) := by
  let jet := globalClosedJet test smooth
  let field := highRobinWeakInverse parameter source
  let probe := highDiskCoreInto jet
  have probeGrade : probe.val = diskCoreInto jet := congrArg diskCoreInto high
  have probeBulk : highDiskBulk probe = closedL2Core jet :=
    (congrArg diskBulk probeGrade).trans (diskBulk_core jet)
  have probeX : highGradX probe = closedL2Core (partialJet 0 jet) :=
    (congrArg diskGradX probeGrade).trans (diskPartial_core 0 jet)
  have probeY : highGradY probe = closedL2Core (partialJet 1 jet) :=
    (congrArg diskGradY probeGrade).trans (diskPartial_core 1 jet)
  have probeTrace : robinTrace probe = 0 :=
    (congrArg diskBoundary probeGrade).trans ((diskBoundary_core jet).trans
      (compactBoundary_zero test smooth supported))
  have equation := highRobinWeakInverse_equation parameter source probe
  change inner ℂ (highGradX probe) (highGradX field) + inner ℂ (highGradY probe) (highGradY field) +
    (parameter ^ 2 : ℝ) * inner ℂ (highDiskBulk probe) (diskB (highDiskBulk field)) +
    2 * inner ℂ (robinTrace probe) (robinTrace field) = inner ℂ (highDiskBulk probe) source.val at equation
  have xEquality := congrArg (fun value : DiskL2 1 => inner ℂ value (highGradX field)) probeX
  have yEquality := congrArg (fun value : DiskL2 1 => inner ℂ value (highGradY field)) probeY
  have massEquality := congrArg (fun value : DiskL2 1 =>
    ((parameter ^ 2 : ℝ) : ℂ) * inner ℂ value (diskB (highDiskBulk field))) probeBulk
  have boundaryEquality : 2 * inner ℂ (robinTrace probe) (robinTrace field) = 0 :=
    (congrArg (fun value : BoundaryL2 => 2 * inner ℂ value (robinTrace field)) probeTrace).trans
      ((congrArg (fun value : ℂ => 2 * value) (inner_zero_left (𝕜 := ℂ) (robinTrace field))).trans (mul_zero _))
  have formEquality := (congrArg₂ (fun first second : ℂ => first + second)
    (congrArg₂ (fun first second : ℂ => first + second)
      (congrArg₂ (fun first second : ℂ => first + second) xEquality yEquality) massEquality)
    boundaryEquality).trans (add_zero _)
  have literalEquation := formEquality.symm.trans (equation.trans
    (congrArg (fun value : DiskL2 1 => inner ℂ value source.val) probeBulk))
  have green := completedGreen_laplacian test smooth compact supported field.val
  have reduced : -inner ℂ (closedL2Core (laplacianJet jet)) (highDiskBulk field) +
      ((parameter ^ 2 : ℝ) : ℂ) * inner ℂ (closedL2Core jet) (diskB (highDiskBulk field)) =
        inner ℂ (closedL2Core jet) source.val := by
    exact (congrArg (fun value : ℂ => value + ((parameter ^ 2 : ℝ) : ℂ) *
      inner ℂ (closedL2Core jet) (diskB (highDiskBulk field))) green).symm.trans literalEquation
  exact (rearrangeGreen _ _ _ reduced).trans
    (inner_smul_sub _ _ _ _).symm

end Grad.CircularHighRegularity
