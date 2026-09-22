import AKDN62ActualNativePureBalancedEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory
open scoped ENNReal ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.AnnularCurrentLow Grad.AnnularHighGenerators Grad.AnnularCoupledInverse
open Grad.AnnularGeneralSourceRegularity Grad.ActualSmoothPhysicalField

variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (field : CoupledSpace lower length positive lengthPositive)
    (curves : ActualSourceRadialCurves parameters lower positive bounded data)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field))

include allGrades

theorem balancedOriginalPairCurve_continuous (grade : ℕ) :
    ContinuousOn (balancedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade) (Icc lower 1) := by
  have inverse : ContinuousOn (fun point : ℝ => point⁻¹) (Icc lower 1) :=
    continuousOn_id.inv₀ (fun point member => (positive.trans_le member.1).ne')
  exact (inverse.smul (conjugatedOriginalPairCurve_continuous parameters lower length positive bounded lengthPositive
    field allGrades (grade+1)).continuousOn.snd).prodMk
    (conjugatedOriginalPairCurve_continuous parameters lower length positive bounded lengthPositive field allGrades grade).continuousOn.fst

/-- The stored seven-slot curve is literally the actual full curve on
both collar endpoints as well as the interior. -/
theorem sameSevenCurve_fullFormula (grade : ℕ) (radius : ℝ) (inside : radius∈Icc lower 1) :
    seven.curve (grade+1) radius =
      balancedSevenInput parameters radius
        (balancedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+1) radius)+
      curves.seven (grade+1) radius := by
  have same : EqOn (seven.curve (grade+1))
      (generalConjugatedFullSevenCurve parameters lower length positive bounded lengthPositive data field curves grade) (Icc lower 1) := by
    apply collarCurve_eq_of_ae lower bounded _ _ (seven.smooth _).continuousOn
      (generalConjugatedFullSevenCurve_continuous parameters lower length positive bounded lengthPositive data field curves allGrades grade)
    filter_upwards [seven.same (grade+1),generalConjugatedFullSevenCurve_actual parameters lower length positive bounded lengthPositive
      data field curves allGrades grade] with point stored full
    apply lp.ext
    funext mode
    exact (stored mode).trans (full mode).symm
  rw [same inside,generalConjugatedFullSevenCurve]
  exact congrArg (fun value => value+curves.seven (grade+1) radius)
    (balancedSevenInput_original parameters lower length positive bounded lengthPositive field allGrades grade radius inside).symm

/-- The fixed projection identity holds everywhere on the closed collar. -/
theorem sameSevenCurve_balancedProjectionOn
    (knownZero : ∀ grade radius, nativeBalancedSevenProjection parameters (curves.seven grade radius)=0)
    (grade : ℕ) :
    EqOn (fun radius => nativeBalancedSevenProjection parameters (seven.curve (grade+1) radius))
      (balancedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade) (Icc lower 1) :=
  collarCurve_eq_of_ae lower bounded _ _
    ((nativeBalancedSevenProjection parameters).continuous.comp_continuousOn (seven.smooth _).continuousOn)
    (balancedOriginalPairCurve_continuous parameters lower length positive bounded lengthPositive field allGrades grade)
    (sameSevenCurve_balancedProjection parameters lower length positive bounded lengthPositive data field curves allGrades seven knownZero grade)

include seven

/-- Actual smoothness of the balanced pair can be read directly from
its exact fixed projection of the SAME stored seven curve. -/
theorem sameSevenCurve_balancedSmooth
    (knownZero : ∀ grade radius, nativeBalancedSevenProjection parameters (curves.seven grade radius)=0)
    (grade : ℕ) :
    ContDiffOn ℝ ∞ (balancedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade) (Icc lower 1) := by
  have smooth := ((nativeBalancedSevenProjection parameters).restrictScalars ℝ).contDiff.comp_contDiffOn (seven.smooth (grade+1))
  exact smooth.congr (sameSevenCurve_balancedProjectionOn parameters lower length positive bounded lengthPositive data field curves allGrades seven knownZero grade).symm

end Grad.OriginalCartesianTameEstimate
