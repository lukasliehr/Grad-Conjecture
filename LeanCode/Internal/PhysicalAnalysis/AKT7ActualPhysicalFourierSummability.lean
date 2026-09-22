import AKT6SamePuncturedGradesAndPhase
import AJY1ExactAngularPrimitiveCurve

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
open Set Filter
open scoped Topology ENNReal
namespace Grad.ActualPuncturedFamily
open Grad.SourceCollarCoefficients Grad.ClosedJets Grad.CartesianState Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularHighGenerators Grad.AnnularRestriction
open Grad.AnnularWeightedSmoothCore Grad.AnnularSmoothCore Grad.AnnularIncomingIntegrability Grad.PhaseAlgebra
open Grad.AnnularPhysicalFourier Grad.AnnularJointRegularity
open Grad.BoundaryKernelAction

/-- A single actual fourth full Fourier grade gives absolute convergence
on the complete two-dimensional mode lattice. -/
theorem fullFourthGrade_summable (base high : CellL2 1)
    (same : ∀ mode : ℤ × ℤ, high mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ 4 : ℝ) : ℂ) • base mode) :
    Summable (fun mode : ℤ × ℤ => ‖base mode‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun mode => ?_) (annularLattice_inverse_four_summable.mul_left ‖high‖)
  change ‖base mode‖ ≤ ‖high‖ * (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ 4)⁻¹
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by unfold Grad.AnnularVariational.annularFrequency; positivity)).mpr
  have bound := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) high mode
  rw [same mode,norm_smul,Complex.norm_real,Real.norm_of_nonneg] at bound
  · exact (mul_comm _ _).trans_le bound
  · unfold Grad.AnnularVariational.annularFrequency
    positivity

variable (parameters : PhaseParameters) (length : ℝ) (lengthPositive : 0 < length)
    (lower : ℕ → ℝ) (positive : ∀ index, 0 < lower index) (bounded : ∀ index, lower index < 1)
    (decreasing : Antitone lower) (cofinal : Tendsto lower atTop (𝓝 0))
    (fields : ∀ index, CoupledSpace (lower index) length (positive index) lengthPositive)
    (allGrades : ∀ index grade, ∃ weighted : CoupledSpace (lower index) length (positive index) lengthPositive,
      CoupledInsertedGrade (lower index) length (positive index) lengthPositive grade (fields index) weighted)
    (compatible : ActualRetainedFamilyCompatible length lengthPositive lower positive bounded decreasing fields)

include compatible

/-- Both actual physical components have convergent full Fourier series. -/
theorem puncturedPhysicalPair_summable (radius : ℝ) (inside : radius ∈ Ioc (0 : ℝ) 1) :
    Summable (fun mode : ℤ × ℤ =>
      ‖(puncturedPhysicalPair parameters length lengthPositive lower positive bounded cofinal fields allGrades 0 radius).1 mode‖) ∧
    Summable (fun mode : ℤ × ℤ =>
      ‖(puncturedPhysicalPair parameters length lengthPositive lower positive bounded cofinal fields allGrades 0 radius).2 mode‖) := by
  have same := puncturedPhysicalPair_grade parameters length lengthPositive lower positive bounded decreasing cofinal fields allGrades compatible 4 radius inside
  exact ⟨fullFourthGrade_summable _ _ (fun mode => congrArg Prod.fst (same mode)),
    fullFourthGrade_summable _ _ (fun mode => congrArg Prod.snd (same mode))⟩

/-- The original pressure p=R^{-1}X has the SAME full Fourier series. -/
theorem puncturedPressure_summable (radius : ℝ) (inside : radius ∈ Ioc (0 : ℝ) 1) :
    Summable (fun mode : ℤ × ℤ =>
      ‖physicalAngularPrimitive parameters
        (puncturedPhysicalPair parameters length lengthPositive lower positive bounded cofinal fields allGrades 0 radius).1 mode‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun mode => ?_)
    (puncturedPhysicalPair_summable parameters length lengthPositive lower positive bounded decreasing cofinal fields allGrades compatible radius inside).1
  rw [physicalAngularPrimitive_apply,norm_smul]
  exact (mul_le_mul_of_nonneg_right (angularInverseMultiplier_norm_le mode) (norm_nonneg _)).trans_eq (one_mul _)

end Grad.ActualPuncturedFamily
