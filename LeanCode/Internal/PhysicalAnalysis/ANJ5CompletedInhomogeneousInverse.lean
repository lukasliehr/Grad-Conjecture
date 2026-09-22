import ANJ4ActualScalarRightInverse

noncomputable section
set_option maxHeartbeats 1200000
namespace Grad.InhomogeneousHighRobin
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.OrdinaryDiskCalculus Grad.ActualUniformGlobal Grad.CircularNormalLift
local instance (priority := 2000) solveUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade
local instance (priority := 2000) solveBoundarySpace (grade : ℕ) : NormedSpace ℂ (normalBoundaryGrade grade) :=
  (normalBoundaryGrade grade).normedSpace

def inhomogeneousCompletedInverse (grade : ℕ) (parameters : PhaseParameters) (parameter : ℝ) :
    (unitDiskSobolev grade × normalBoundaryGrade (grade + 2)) →L[ℂ] unitDiskSobolev (grade + 2) :=
  let lift := (completedNormalLift (grade + 2)).comp
    (ContinuousLinearMap.snd ℂ (unitDiskSobolev grade) (normalBoundaryGrade (grade + 2)))
  lift + (actualCompletedInverse grade parameters parameter).comp
    (ContinuousLinearMap.fst ℂ _ _ - (unitScalarOperator grade parameter).comp lift)

theorem inhomogeneousCompletedInverse_apply (grade : ℕ) (parameters : PhaseParameters) (parameter : ℝ)
    (source : unitDiskSobolev grade) (boundary : normalBoundaryGrade (grade + 2)) :
    inhomogeneousCompletedInverse grade parameters parameter (source, boundary) =
      completedNormalLift (grade + 2) boundary + actualCompletedInverse grade parameters parameter
        (source - unitScalarOperator grade parameter (completedNormalLift (grade + 2) boundary)) := rfl

private theorem correctedNorm_bound {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F] (inverse : E →L[ℂ] F) (operator : F →L[ℂ] E)
    (source : E) (lift : F) (inputNorm liftConstant inverseConstant operatorConstant : ℝ)
    (inputNonnegative : 0 ≤ inputNorm) (liftNonnegative : 0 ≤ liftConstant)
    (inverseNonnegative : 0 ≤ inverseConstant) (operatorNonnegative : 0 ≤ operatorConstant)
    (liftBound : ‖lift‖ ≤ liftConstant * inputNorm)
    (inverseBound : ∀ value, ‖inverse value‖ ≤ inverseConstant * ‖value‖)
    (operatorBound : ∀ value, ‖operator value‖ ≤ operatorConstant * ‖value‖) :
    ‖lift + inverse (source - operator lift)‖ ≤
      (inverseConstant + (1 + inverseConstant * operatorConstant) * liftConstant) * (‖source‖ + inputNorm) := by
  have forced := (norm_sub_le source (operator lift)).trans
    (add_le_add le_rfl ((operatorBound lift).trans (mul_le_mul_of_nonneg_left liftBound operatorNonnegative)))
  have corrected := (inverseBound (source - operator lift)).trans
    (mul_le_mul_of_nonneg_left forced inverseNonnegative)
  have total := (norm_add_le lift (inverse (source - operator lift))).trans (add_le_add liftBound corrected)
  apply total.trans
  have first := mul_nonneg
    (mul_nonneg (add_nonneg zero_le_one (mul_nonneg inverseNonnegative operatorNonnegative)) liftNonnegative)
    (norm_nonneg source)
  have second := mul_nonneg inverseNonnegative inputNonnegative
  nlinarith

def inhomogeneousInverseConstant (grade : ℕ) (ceiling : ℝ) : ℝ :=
  finiteInverseConstant grade ceiling +
    (1 + finiteInverseConstant grade ceiling * scalarOperatorConstant grade ceiling) *
      Real.sqrt (normalSobolevConstant (grade + 2))

theorem inhomogeneousInverseConstant_nonnegative (grade : ℕ) (ceiling : ℝ) :
    0 ≤ inhomogeneousInverseConstant grade ceiling :=
  add_nonneg (finiteInverseConstant_nonnegative grade ceiling)
    (mul_nonneg (add_nonneg zero_le_one
      (mul_nonneg (finiteInverseConstant_nonnegative grade ceiling) (scalarOperatorConstant_nonnegative grade ceiling)))
      (Real.sqrt_nonneg _))

theorem inhomogeneousCompletedInverse_bound (grade : ℕ) (ceiling : ℝ) (parameters : PhaseParameters)
    (parameter : ℝ) (bounded : |parameter| ≤ ceiling)
    (source : unitDiskSobolev grade) (boundary : normalBoundaryGrade (grade + 2)) :
    ‖inhomogeneousCompletedInverse grade parameters parameter (source, boundary)‖ ≤
      inhomogeneousInverseConstant grade ceiling * (‖source‖ + ‖boundary‖) :=
  @correctedNorm_bound (unitDiskSobolev grade) (unitDiskSobolev (grade + 2))
    inferInstance inferInstance (unitNormedSpace grade) (unitNormedSpace (grade + 2))
    (actualCompletedInverse grade parameters parameter) (unitScalarOperator grade parameter)
    source (completedNormalLift (grade + 2) boundary) ‖boundary‖
    (Real.sqrt (normalSobolevConstant (grade + 2))) (finiteInverseConstant grade ceiling) (scalarOperatorConstant grade ceiling)
    (norm_nonneg boundary) (Real.sqrt_nonneg _) (finiteInverseConstant_nonnegative grade ceiling)
    (scalarOperatorConstant_nonnegative grade ceiling) (completedNormalLift_bound (grade + 2) (by omega) boundary)
    (actualCompletedInverse_bound grade ceiling parameters parameter bounded)
    (unitScalarOperator_bound grade ceiling parameter bounded)

theorem inhomogeneousCompletedInverse_robin (grade : ℕ) (parameters : PhaseParameters) (parameter : ℝ)
    (source : unitDiskSobolev grade) (boundary : normalBoundaryGrade (grade + 2)) :
    ordinaryRobinTrace grade (inhomogeneousCompletedInverse grade parameters parameter (source, boundary)) = boundary.val := by
  have addition := (ordinaryRobinTrace grade).map_add (completedNormalLift (grade + 2) boundary)
    (actualCompletedInverse grade parameters parameter
      (source - unitScalarOperator grade parameter (completedNormalLift (grade + 2) boundary)))
  exact addition.trans ((congrArg₂ (fun first second => first + second)
    (completedNormalLift_robin_trace grade boundary) (actualCompletedInverse_robin_zero grade parameters parameter _)).trans
      (add_zero _))

theorem inhomogeneousCompletedInverse_scalar (grade : ℕ) (parameters : PhaseParameters) (parameter : ℝ)
    (source : unitDiskSobolev grade) (sourceHigh : unitDiskBulk grade source ∈ highDiskL2)
    (boundary : normalBoundaryGrade (grade + 2))
    (boundaryHigh : ∀ mode ∈ lowAngularModes, normalBoundaryCoefficient (grade + 2) boundary mode = 0) :
    unitScalarOperator grade parameter (inhomogeneousCompletedInverse grade parameters parameter (source, boundary)) = source := by
  have liftHigh := completedNormalLift_high (grade + 2) (by omega) boundary boundaryHigh
  have imageHigh := unitScalarOperator_high parameters grade parameter _ liftHigh
  have forcingHigh : unitDiskBulk grade (source - unitScalarOperator grade parameter (completedNormalLift (grade + 2) boundary)) ∈ highDiskL2 :=
    ((unitDiskBulk grade).map_sub _ _).symm ▸ highDiskL2.sub_mem sourceHigh imageHigh
  have corrected := actualCompletedInverse_scalar_high parameters grade parameter _ forcingHigh
  exact ((unitScalarOperator grade parameter).map_add _ _).trans
    ((congrArg (fun correction => unitScalarOperator grade parameter (completedNormalLift (grade + 2) boundary) + correction) corrected).trans
      (by abel))

theorem inhomogeneousCompletedInverse_high (grade : ℕ) (parameters : PhaseParameters) (parameter : ℝ)
    (source : unitDiskSobolev grade) (boundary : normalBoundaryGrade (grade + 2))
    (boundaryHigh : ∀ mode ∈ lowAngularModes, normalBoundaryCoefficient (grade + 2) boundary mode = 0) :
    unitDiskBulk (grade + 2) (inhomogeneousCompletedInverse grade parameters parameter (source, boundary)) ∈ highDiskL2 :=
  ((unitDiskBulk (grade + 2)).map_add _ _).symm ▸
    highDiskL2.add_mem (completedNormalLift_high (grade + 2) (by omega) boundary boundaryHigh)
      (actualCompletedInverse_high parameters grade parameter _)

end Grad.InhomogeneousHighRobin
