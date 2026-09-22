import AKCY10ActualNewtonQuadraticRemainder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3500
open Set

namespace Grad.NashMoser.OriginalIteration
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.SmoothingFamily Grad.Q24Realization Grad.NashMoser.OriginalLimit Grad.NashMoser.Numeric
open Grad.PhysicalCoordinates

attribute [local irreducible] originalNonlinearSource literalPhysicalSmoothForward
  originalLiteralTaylorRemainder originalStateSmoothing

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}

namespace OriginalNewtonInverse
variable (inverse : OriginalNewtonInverse neighborhood cellLength loss)

/-- The actual all-cutoff NM07 recurrence is derived for a finite stage.
The high bounds and admissible chord are visible inputs at this internal
boundary; the following Stage constructor derives both from its budgets. -/
theorem actual_stage_recurrence (lossLarge : 6 ≤ loss) (initial : ℝ) (initialLarge : 4 ≤ initial)
    (finite : OriginalFiniteParameter) (member : finite ∈ neighborhood.parameterDomain)
    (state : stateSmoothRange parameters reference inside)
    (low : stateSize parameters reference inside base loss state ≤ neighborhood.radius) (index : ℕ)
    (coarse : ∀ grade, stateSize parameters reference inside base grade state ≤
      inverse.correctionConstant grade * previousStageTime initial index ^ (grade:ℝ))
    (residualSmall : inverse.residualSize finite state ≤ 1)
    (chord : ∀ t ∈ Icc (0:ℝ) 1,
      stateSize parameters reference inside base 0
        (state+t•inverse.correction finite state (newtonTime initial index)) ≤ 2*neighborhood.radius)
    (cutoff : ℕ) :
    inverse.residualSize finite (state+inverse.correction finite state (newtonTime initial index)) ≤
      inverse.quadraticConstant lossLarge * newtonTime initial index ^ (2*(loss:ℝ)) *
        (inverse.residualSize finite state)^2 +
      inverse.defectConstant lossLarge cutoff * newtonTime initial index ^ (-(((cutoff:ℝ)-8*loss)/3)) := by
  have positive : 0 < initial := by linarith
  have scalePositive := newtonTime_pos positive index
  have scaleLarge : 1 ≤ newtonTime initial index :=
    (by linarith : 1 ≤ initial).trans (newtonTime_lower (by linarith) index)
  have previousLarge := previousStageTime_one_le initial (by linarith) index
  have previousLe : previousStageTime initial index ≤ newtonTime initial index := by
    have bound := Real.rpow_le_rpow_of_exponent_le scaleLarge (by norm_num : (2/3:ℝ) ≤ 1)
    simpa only [previousStageTime,Real.rpow_one] using bound
  let lowBase : stateSize parameters reference inside base 0 state ≤ 2*neighborhood.radius :=
    ((stateSize_mono parameters reference inside base (Nat.zero_le loss) state).trans low).trans
      (by linarith [neighborhood.radiusPositive])
  let axis := neighborhood.axis state lowBase
  let seed := neighborhood.patchInside (neighborhood.seedInside finite member)
  let next := state+inverse.correction finite state (newtonTime initial index)
  let forward := literalPhysicalSmoothForward parameters cellLength reference inside finite.1 seed (finite.2,state) axis
  let remainder := originalLiteralTaylorRemainder parameters cellLength reference inside (finite.1,finite.2,state)
    seed axis (finite.1,finite.2,next)
  have identity : inverse.residual finite next =
      forward (inverse.smoothingDefect finite state (newtonTime initial index))+remainder :=
    smoothedNewton_residual_identity parameters reference inside cellLength finite seed
      (newtonTime initial index) state axis (inverse.map finite state)
        (inverse.right finite member state lowBase (inverse.residual finite state))
  have linearBound := inverse.forward_smoothingDefect_bound lossLarge finite member state low
    (newtonTime initial index) (previousStageTime initial index) scalePositive previousLarge coarse residualSmall cutoff
  have quadraticBound := inverse.quadraticRemainder_bound lossLarge finite member state low
    (newtonTime initial index) (previousStageTime initial index) scaleLarge previousLarge previousLe
      coarse residualSmall chord
  change sourceSize parameters base loss (forward (inverse.smoothingDefect finite state (newtonTime initial index))) ≤ _ at linearBound
  change sourceSize parameters base loss remainder ≤ _ at quadraticBound
  change sourceSize parameters base loss (inverse.residual finite next) ≤ _
  rw [identity]
  have total := (map_add_le_add (sourceSize parameters base loss) _ _).trans
    (add_le_add linearBound quadraticBound)
  apply total.trans_eq
  rw [mul_assoc (inverse.defectConstant lossLarge cutoff),smoothingDefect_power initial positive index cutoff loss]
  ring

end OriginalNewtonInverse
end Grad.NashMoser.OriginalIteration
