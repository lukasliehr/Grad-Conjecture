import AKDS18FullSourceReferenceAssembly
import QYP13PhysicalInnerFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
namespace Grad.OriginalCoreRealization
open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds Grad.RealFixedRanges
open Grad.ChartAxisLift Grad.Q24Realization Grad.SmoothingFamily Grad.PhysicalCoordinates
open Grad.MixedQuotientComposition Grad.FinitePhysicalJetLift Grad.NonlinearProduct
open Grad.GaugeCoefficients.Physical.Allocation

/-- The actual physical coefficient budget has a same-grade bound in the
original reference state. The constants are uniform on the fixed seed patch
and finite curvature/seed bounds; no high state norm is constrained. -/
theorem actualPhysicalBudget_reference_bound (parameters : PhaseParameters) (grade : ℕ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) (curvatureBound seedBound : ℝ) :
    ∃ constant : ℝ,0≤constant ∧ ∀ seed ∈ seedPatch, ∀ (insideS : seed ∈ Seed.parameterDomain)
      (base : RealJointCore parameters reference insideR), |base.1|≤curvatureBound → |seed 0|≤seedBound →
      ChartAxisCondition (smoothingChartCore parameters base.2.val) →
      physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
        (seed 0) base.1 grade ≤ constant*(1+‖stateToGrade parameters grade base.2.val‖) := by
  obtain ⟨innerConstant,innerNonnegative,innerBound⟩ := physicalMixedInnerFamily_bound parameters reference insideR
    grade 0 seedPatch compact insidePatch curvatureBound
  let fixed := originalGradeNorm grade (planarReferenceCore parameters)+|seedBound|+|curvatureBound|
  have fixedNonnegative : 0≤fixed := add_nonneg
    (add_nonneg (originalGradeNorm_nonnegative _ _) (abs_nonneg _)) (abs_nonneg _)
  refine ⟨innerConstant+fixed,add_nonneg innerNonnegative fixedNonnegative,?_⟩
  intro seed seedIn insideS base curvature seedSmall axis
  let input : Input parameters := (seed,realJointCoreToJoint parameters reference insideR base)
  have curvatureNorm : ‖input.2.1‖≤curvatureBound := by
    change ‖(base.1:ℂ)‖≤curvatureBound
    simpa only [Complex.norm_real,Real.norm_eq_abs] using curvature
  have physicalBound := innerBound input (fun index => Fin.elim0 index) seedIn curvatureNorm axis
  rw [physicalMixedInnerFamily_zero parameters reference insideR input insideS,
    actualFiniteCurrentState_eq] at physicalBound
  simp only [inputOneHigh,Fin.prod_univ_zero,Fin.sum_univ_zero,mul_one,add_zero] at physicalBound
  have sameState : baseNorm grade input=‖stateToGrade parameters grade base.2.val‖ := by
    rw [axb_stateToGrade_literal_norm]
    rfl
  rw [sameState] at physicalBound
  have currentBound := Grad.NonlinearQuotientBounds.originalGradeNorm_sub_le grade
    (planarReferenceCore parameters+actualFiniteCurrentField parameters reference insideR seed insideS base)
    (planarReferenceCore parameters)
  rw [add_sub_cancel_left] at currentBound
  have vectorBound : originalGradeNorm grade
      (planarReferenceCore parameters+actualFiniteCurrentField parameters reference insideR seed insideS base) ≤
      innerConstant*(1+‖stateToGrade parameters grade base.2.val‖) := by
    dsimp only [stateNorm] at physicalBound
    linarith [norm_nonneg (base.1:ℂ),originalGradeNorm_nonnegative grade
      (actualFiniteCurrentScalar parameters reference insideR seed insideS base)]
  have raw : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
      (seed 0) base.1 grade ≤ innerConstant*(1+‖stateToGrade parameters grade base.2.val‖)+fixed := by
    dsimp only [physicalBudget,fixed]
    linarith [le_abs_self seedBound,le_abs_self curvatureBound]
  exact raw.trans (by nlinarith [mul_nonneg fixedNonnegative (norm_nonneg
    (stateToGrade parameters grade base.2.val))])

end Grad.OriginalCoreRealization
