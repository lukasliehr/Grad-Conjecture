import AUB3UniformGlobalInduction
import ARW10UniformOuterGain
import AST4CoreProjectionEnergy

noncomputable section
set_option maxHeartbeats 1000000
namespace Grad.ActualUniformGlobal
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.ActualFiniteGlobal Grad.OrdinaryDiskFaithfulness Grad.OrdinaryDiskCalculus
open Grad.ActualRadialWords Grad.AngularSobolevTruncation
open Grad.GaugeCoefficients.Algebra
attribute [local instance] unitNormedSpace

theorem selectedCore_uniform_bound (grade : ℕ) (modes : Finset ℤ) (core : ClosedJet 1) :
    ‖unitDiskCoreInto grade (selectedAngularJet modes core)‖ ≤
      orthogonalGradeConstant grade ^ 2 * ‖unitDiskCoreInto grade core‖ := by
  simpa only [unitDiskCore_norm] using coreSelected_uniform_bound grade modes core

private theorem norm_sub_of_bound {E : Type*} [SeminormedAddCommGroup E]
    (first second : E) (constant : ℝ) (bound : ‖second‖ ≤ constant * ‖first‖) :
    ‖first - second‖ ≤ (1 + constant) * ‖first‖ := by
  calc
    ‖first - second‖ ≤ ‖first‖ + ‖second‖ := norm_sub_le first second
    _ ≤ ‖first‖ + constant * ‖first‖ := add_le_add le_rfl bound
    _ = (1 + constant) * ‖first‖ := by ring

theorem excludedCore_uniform_bound (grade : ℕ) (core : ClosedJet 1) :
    ‖unitDiskCoreInto grade (excludedAngularJet lowAngularModes core)‖ ≤
      (1 + orthogonalGradeConstant grade ^ 2) * ‖unitDiskCoreInto grade core‖ := by
  have identity : unitDiskCoreInto grade (excludedAngularJet lowAngularModes core) =
      unitDiskCoreInto grade core - unitDiskCoreInto grade (selectedAngularJet lowAngularModes core) :=
    (unitDiskCoreInto grade).map_sub core (selectedAngularJet lowAngularModes core)
  have estimate : ‖unitDiskCoreInto grade core - unitDiskCoreInto grade (selectedAngularJet lowAngularModes core)‖ ≤
      (1 + orthogonalGradeConstant grade ^ 2) * ‖unitDiskCoreInto grade core‖ :=
    norm_sub_of_bound _ _ _ (selectedCore_uniform_bound grade lowAngularModes core)
  exact (congrArg norm identity).trans_le estimate

/-- Actual homogeneous global two-derivative estimate for finite angular
sources. No regularity or collar bound is a premise, and C depends only on
s and the fixed parameter interval, before every cutoff and source. -/
theorem finiteGlobal_actual_uniform_gain (grade : ℕ) (ceiling : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (parameters : PhaseParameters) (parameter : ℝ),
      |parameter| ≤ ceiling → ∀ (source : highDiskL2) (core : ClosedJet 1)
      (same : source.val = closedL2Core core) (modes : Finset ℤ),
      ‖finiteGlobalRepresentative parameters modes parameter source core same (grade + 2)‖ ≤
        constant * ‖unitDiskCoreInto grade core‖ := by
  choose constants nonnegative bounds using (fun order => finiteOuterWithinOrdinary_gain order ceiling)
  exact finiteGlobal_uniform_of_outer grade ceiling (fun order => orthogonalGradeConstant order ^ 2)
    constants (fun _ => sq_nonneg _) nonnegative
    (fun order modes core => selectedCore_uniform_bound order modes core)
    (fun order parameter parameterBound source core same modes => bounds order parameter parameterBound source core same modes)

/-- The actual smooth finite inverse is a uniformly bounded linear map from
ordinary Hs to H^(s+2), after removal of exactly the five low modes. -/
theorem finiteSmoothInverse_uniform_gain (grade : ℕ) (ceiling : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (parameters : PhaseParameters) (parameter : ℝ),
      |parameter| ≤ ceiling → ∀ (modes : Finset ℤ) (core : ClosedJet 1),
      ‖unitDiskCoreInto (grade + 2) (finiteSmoothInverseLinear parameters modes parameter core)‖ ≤
        constant * ‖unitDiskCoreInto grade core‖ := by
  obtain ⟨constant, nonnegative, bound⟩ := finiteGlobal_actual_uniform_gain grade ceiling
  refine ⟨constant * (1 + orthogonalGradeConstant grade ^ 2), mul_nonneg nonnegative (by positivity), ?_⟩
  intro parameters parameter parameterBound modes core
  have identification : unitDiskCoreInto (grade + 2) (finiteSmoothInverseLinear parameters modes parameter core) =
      finiteGlobalRepresentative parameters modes parameter (highL2Core core)
        (excludedAngularJet lowAngularModes core) (highL2Projection_core core) (grade + 2) :=
    finiteInverseClosedJet_grade parameters modes parameter (highL2Core core)
      (excludedAngularJet lowAngularModes core) (highL2Projection_core core) (grade + 2)
  rw [identification]
  exact (bound parameters parameter parameterBound (highL2Core core)
    (excludedAngularJet lowAngularModes core) (highL2Projection_core core) modes).trans
    ((mul_le_mul_of_nonneg_left (excludedCore_uniform_bound grade core) nonnegative).trans_eq (by ring))

end Grad.ActualUniformGlobal
