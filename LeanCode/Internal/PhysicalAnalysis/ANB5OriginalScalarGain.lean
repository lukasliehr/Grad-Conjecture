import ANB4ExactScalarInverseLaws

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.BoundedScalarInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.ActualCenterBounds Grad.InhomogeneousHighRobin Grad.CircularNormalLift Grad.AngularSobolevTruncation
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Algebra Grad.OrdinaryDiskCalculus
local instance (priority := 2000) scalarGainUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade

private theorem linear_three_norm {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (linear : V →ₗ[ℂ] W) (first second third : V) :
    ‖linear (first + second + third)‖ ≤ ‖linear first‖ + ‖linear second‖ + ‖linear third‖ := by
  rw [map_add, map_add]
  exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

theorem originalMode_norm (grade : ℕ) (mode : ℤ) (field : ClosedJet 1) :
    ‖unitDiskCoreInto grade (angularClosedJet mode field)‖ ≤ orthogonalGradeConstant grade * ‖unitDiskCoreInto grade field‖ :=
  (congrArg norm (ordinaryMode_core grade mode field)).symm.le.trans (ordinaryMode_bound grade mode _)

theorem originalHigh_norm (grade : ℕ) (field : ClosedJet 1) :
    ‖unitDiskCoreInto grade (excludedAngularJet lowAngularModes field)‖ ≤
      (1 + orthogonalGradeConstant grade ^ 2) * ‖unitDiskCoreInto grade field‖ := by
  have same := ((unitDiskCoreInto grade).map_sub field (selectedAngularJet lowAngularModes field)).trans
    (congrArg (fun value : unitDiskSobolev grade => unitDiskCoreInto grade field - value)
      (ordinarySelected_core grade lowAngularModes field).symm)
  exact (congrArg norm same).le.trans ((norm_sub_le _ _).trans
    ((add_le_add le_rfl (ordinarySelected_uniform_bound grade lowAngularModes (unitDiskCoreInto grade field))).trans_eq
      (one_add_mul (orthogonalGradeConstant grade ^ 2) ‖unitDiskCoreInto grade field‖).symm))

def scalarGainConstant (grade : ℕ) (large : 3 ≤ grade) (ceiling : ℝ) : ℝ :=
  2 * centerNativeGainConstant grade large ceiling * orthogonalGradeConstant grade +
    inhomogeneousInverseConstant grade ceiling * (1 + orthogonalGradeConstant grade ^ 2) + inhomogeneousInverseConstant grade ceiling

theorem scalarGainConstant_nonnegative (grade : ℕ) (large : 3 ≤ grade) (ceiling : ℝ) :
    0 ≤ scalarGainConstant grade large ceiling := by
  unfold scalarGainConstant
  exact add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (centerNativeGainConstant_nonnegative grade large ceiling)) (orthogonalGradeConstant_nonnegative grade))
      (mul_nonneg (inhomogeneousInverseConstant_nonnegative grade ceiling) (by positivity)))
    (inhomogeneousInverseConstant_nonnegative grade ceiling)

private theorem combine_scalar_gain (value source boundary center high projection angular : ℝ)
    (sourceNonnegative : 0 ≤ source) (boundaryNonnegative : 0 ≤ boundary)
    (centerNonnegative : 0 ≤ center) (highNonnegative : 0 ≤ high)
    (projectionNonnegative : 0 ≤ projection) (angularNonnegative : 0 ≤ angular)
    (bound : value ≤ center * (angular * source) + center * (angular * source) + high * (projection * source + boundary)) :
    value ≤ (2 * center * angular + high * projection + high) * (source + boundary) := by
  have first := mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) centerNonnegative)
    angularNonnegative) (mul_nonneg highNonnegative projectionNonnegative)) boundaryNonnegative
  have second := mul_nonneg highNonnegative sourceNonnegative
  nlinarith

/-- The common actual scalar inverse gains two original Cartesian grades.
Constants precede phase parameters, bounded k, source and actual boundary datum. -/
theorem scalarInverseJet_native_gain (grade : ℕ) (large : 3 ≤ grade) (ceiling : ℝ)
    (parameters : PhaseParameters) (frequency : ℝ) (bounded : |frequency| ≤ ceiling)
    (source : ClosedJet 1) (boundary : NormalSmoothBoundary) :
    ‖unitDiskCoreInto (grade + 2) (scalarInverseJet parameters frequency source boundary)‖ ≤
      scalarGainConstant grade large ceiling * (‖unitDiskCoreInto grade source‖ + ‖boundary.grade grade‖) := by
  have centerBound (mode : ℤ) (center : mode = 1 ∨ mode = -1) :
      ‖unitDiskCoreInto (grade + 2) (scalarCenterPart mode frequency source)‖ ≤
        centerNativeGainConstant grade large ceiling * (orthogonalGradeConstant grade * ‖unitDiskCoreInto grade source‖) :=
    (pinnedCenterSolution_native_gain grade large ceiling mode center frequency bounded _ (angularClosedJet_pure mode source)).trans
      (mul_le_mul_of_nonneg_left (originalMode_norm grade mode source) (centerNativeGainConstant_nonnegative grade large ceiling))
  have highBound := (inhomogeneousSmoothInverse_bound grade ceiling parameters frequency bounded
    (excludedAngularJet lowAngularModes source) boundary).trans
      (mul_le_mul_of_nonneg_left (add_le_add (originalHigh_norm grade source) le_rfl)
        (inhomogeneousInverseConstant_nonnegative grade ceiling))
  have triangle := @linear_three_norm (ClosedJet 1) (unitDiskSobolev (grade + 2))
    inferInstance inferInstance inferInstance (unitNormedSpace (grade + 2)) (unitDiskCoreInto (grade + 2))
    (scalarCenterPart 1 frequency source) (scalarCenterPart (-1) frequency source) (scalarHighPart parameters frequency source boundary)
  exact combine_scalar_gain _ _ _ _ _ _ _ (norm_nonneg _) (norm_nonneg _)
    (centerNativeGainConstant_nonnegative grade large ceiling) (inhomogeneousInverseConstant_nonnegative grade ceiling)
    (by positivity) (orthogonalGradeConstant_nonnegative grade)
    (triangle.trans (add_le_add (add_le_add (centerBound 1 (Or.inl rfl)) (centerBound (-1) (Or.inr rfl))) highBound))

theorem actual_nonexceptional_scalar_native_solver (grade : ℕ) (large : 3 ≤ grade) (ceiling : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (_parameters : PhaseParameters) (frequency : ℝ), |frequency| ≤ ceiling →
      ∀ source : ClosedJet 1, IsScalarNonexceptional source → ∀ boundary : NormalSmoothBoundary, BoundaryIsHigh boundary →
        ∃! solution : ClosedJet 1, IsNonexceptionalScalarSolution frequency source boundary solution ∧
          ‖unitDiskCoreInto (grade + 2) solution‖ ≤ constant * (‖unitDiskCoreInto grade source‖ + ‖boundary.grade grade‖) := by
  refine ⟨scalarGainConstant grade large ceiling, scalarGainConstant_nonnegative grade large ceiling, ?_⟩
  intro parameters frequency bounded source excluded boundary high
  exact ⟨scalarInverseJet parameters frequency source boundary,
    ⟨scalarInverseJet_specification parameters frequency source excluded boundary high,
      scalarInverseJet_native_gain grade large ceiling parameters frequency bounded source boundary⟩,
    fun candidate laws => scalarInverseJet_unique parameters frequency source boundary high candidate laws.1⟩

end Grad.BoundedScalarInverse
