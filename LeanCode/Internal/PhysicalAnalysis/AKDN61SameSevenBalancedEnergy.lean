import AKDN60PurePairSevenProjection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory
open scoped ENNReal
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.AnnularCurrentLow Grad.AnnularHighGenerators Grad.AnnularCoupledInverse
open Grad.AnnularGeneralSourceRegularity Grad.ActualSmoothPhysicalField

/-- Exact recovery from the SAME seven-packet realization at one extra
pure frequency grade. The prescribed slots are killed by the fixed projection. -/
theorem sameSevenCurve_balancedProjection (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (field : CoupledSpace lower length positive lengthPositive)
    (curves : ActualSourceRadialCurves parameters lower positive bounded data)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field))
    (knownZero : ∀ grade radius, nativeBalancedSevenProjection parameters (curves.seven grade radius)=0)
    (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      nativeBalancedSevenProjection parameters (seven.curve (grade+1) radius) =
        balancedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade radius := by
  filter_upwards [generalConjugatedFullSevenCurve_actual parameters lower length positive bounded lengthPositive data field curves allGrades grade,
    seven.same (grade+1),ae_restrict_mem measurableSet_Icc] with radius full stored inside
  have sameSeven : seven.curve (grade+1) radius =
      generalConjugatedFullSevenCurve parameters lower length positive bounded lengthPositive data field curves grade radius := by
    apply lp.ext
    funext mode
    exact (stored mode).trans (full mode).symm
  rw [sameSeven,generalConjugatedFullSevenCurve,map_add,knownZero,add_zero]
  have original := balancedSevenInput_original parameters lower length positive bounded lengthPositive field allGrades grade radius inside
  change balancedSevenInput parameters radius
      (balancedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+1) radius) =
    generalConjugatedUnknownSevenCurve parameters lower length positive bounded lengthPositive field grade radius at original
  rw [←original]
  apply nativeBalancedSevenProjection_recovers
  intro mode
  simpa only [pow_one] using balancedOriginalPairCurve_shift parameters lower length positive bounded lengthPositive
    field allGrades grade 1 radius inside mode

theorem sameSevenCurve_balancedEnergy (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (field : CoupledSpace lower length positive lengthPositive)
    (curves : ActualSourceRadialCurves parameters lower positive bounded data)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field))
    (knownZero : ∀ grade radius, nativeBalancedSevenProjection parameters (curves.seven grade radius)=0)
    (grade : ℕ) (payment : ℝ)
    (energy : (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖seven.curve (grade+1) radius‖^2)) ≤ ENNReal.ofReal (payment^2)) :
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖balancedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade radius‖^2)) ≤
      ENNReal.ofReal ((‖nativeBalancedSevenProjection parameters‖*payment)^2) := by
  have same := sameSevenCurve_balancedProjection parameters lower length positive bounded lengthPositive data field curves allGrades seven knownZero grade
  have integralSame : (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖balancedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade radius‖^2)) =
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖nativeBalancedSevenProjection parameters (seven.curve (grade+1) radius)‖^2)) := by
    apply lintegral_congr_ae
    filter_upwards [same] with radius same
    rw [same]
  exact integralSame.le.trans (boundedAction_squareEnergy lower (nativeBalancedSevenProjection parameters) (seven.curve (grade+1)) payment energy)

end Grad.OriginalCartesianTameEstimate
