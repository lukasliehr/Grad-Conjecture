import ANR45BoundaryCharacterPairing

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak

/-- The actual AN18 equation against a high character with arbitrary
outer trace, rearranged with its already constructed literal L2 Laplacian. -/
theorem weakInverse_boundary_form (parameter : ℝ) (source : highDiskL2)
    (mode : ℤ) (high : mode ∉ lowAngularModes) (vector : ComplexEuclidean 1)
    (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test) (away : (0 : ℝ) ∉ tsupport test) :
    let jet := boundaryCharacterJet mode vector test smooth away
    let solution := (highRobinWeakInverse parameter source).val
    inner ℂ (diskGradX (diskCoreInto jet)) (diskGradX solution) +
      inner ℂ (diskGradY (diskCoreInto jet)) (diskGradY solution) +
      inner ℂ (closedL2Core jet) (weakLaplacianValue parameter source) +
      2 * inner ℂ (diskBoundary (diskCoreInto jet)) (diskBoundary solution) = 0 := by
  dsimp only
  let jet := boundaryCharacterJet mode vector test smooth away
  let solution := highRobinWeakInverse parameter source
  let trial := highDiskCoreInto jet
  let evaluation : diskGrade → ℂ := fun field =>
    inner ℂ (diskGradX field) (diskGradX solution.val) +
    inner ℂ (diskGradY field) (diskGradY solution.val) +
    ((parameter ^ 2 : ℝ) : ℂ) * inner ℂ (diskBulk field) (diskB (highDiskBulk solution)) +
    2 * inner ℂ (diskBoundary field) (diskBoundary solution.val)
  have underlying : trial.val = diskCoreInto jet := boundaryCharacter_highCore mode high vector test smooth away
  have left : robinValue parameter solution trial = evaluation (diskCoreInto jet) := congrArg evaluation underlying
  have bulk : highDiskBulk trial = closedL2Core jet :=
    (congrArg diskBulk underlying).trans (diskBulk_core jet)
  have right := congrArg (fun value : DiskL2 1 => inner ℂ value source.val) bulk
  have equation := left.symm.trans ((highRobinWeakInverse_equation parameter source trial).trans right)
  have bulkCore := diskBulk_core jet
  have mass : inner ℂ (diskBulk (diskCoreInto jet)) (diskB (highDiskBulk solution)) =
      inner ℂ (closedL2Core jet) (diskB (highDiskBulk solution)) :=
    congrArg (fun value : DiskL2 1 => inner ℂ value (diskB (highDiskBulk solution))) bulkCore
  let pairing : DiskL2 1 →L[ℂ] ℂ := innerSL ℂ (closedL2Core jet)
  let scalar : ℂ := ((parameter ^ 2 : ℝ) : ℂ)
  change inner ℂ (diskBulk (diskCoreInto jet)) (diskB (highDiskBulk solution)) =
    pairing (diskB (highDiskBulk solution)) at mass
  have laplacian : pairing (weakLaplacianValue parameter source) =
      scalar * pairing (diskB (highDiskBulk solution)) - pairing source.val := by
    change pairing (scalar • diskB (highDiskBulk solution) - source.val) = _
    exact (pairing.map_sub _ _).trans
      (congrArg (fun value : ℂ => value - pairing source.val) (pairing.map_smul scalar _))
  change inner ℂ (diskGradX (diskCoreInto jet)) (diskGradX solution.val) +
    inner ℂ (diskGradY (diskCoreInto jet)) (diskGradY solution.val) +
    scalar * inner ℂ (diskBulk (diskCoreInto jet)) (diskB (highDiskBulk solution)) +
    2 * inner ℂ (diskBoundary (diskCoreInto jet)) (diskBoundary solution.val) = pairing source.val at equation
  change inner ℂ (diskGradX (diskCoreInto jet)) (diskGradX solution.val) +
    inner ℂ (diskGradY (diskCoreInto jet)) (diskGradY solution.val) +
    pairing (weakLaplacianValue parameter source) +
    2 * inner ℂ (diskBoundary (diskCoreInto jet)) (diskBoundary solution.val) = 0
  linear_combination equation + laplacian - scalar * mass

end Grad.CircularHighRegularity
