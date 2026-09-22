import AKCK10ActualSameSourceFourOrderEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularGeneralSourceRegularity Grad.AnnularWeightedSmoothness
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularStrongData Grad.AnnularSmoothCore
open Grad.AnnularCurrentLow

/-- Exact immediate consumer: the estimated bulk action is the already
constructed original conjugated known row, evaluated at the literal radius. -/
theorem balancedActualSource_sameKnownCurves (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (curves : ActualSourceRadialCurves parameters lower positive bounded data)
    (grade : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    balancedActualSource parameters length compact lower positive bounded state data curves grade
        (collarRadius lower positive bounded.le radius) =
      balancedFluxOutput parameters length radius
        (generalConjugatedKnownRowCurve parameters length compact lower positive bounded state data curves 0 (grade+1) radius,
         (generalConjugatedKnownRowCurve parameters length compact lower positive bounded state data curves 1 (grade+1) radius,
          generalConjugatedKnownRowCurve parameters length compact lower positive bounded state data curves 2 (grade+1) radius)) +
      (hilbertMeanFree parameters (curves.force (grade+1) radius),
        hilbertFrequencyOperator parameters 1 (some false) (curves.third (grade+1) radius)) := by
  have same (row : Fin 3) :
      generalConjugatedKnownRowCurve parameters length compact lower positive bounded state data curves row (grade+1) radius =
      bulkKernelAction parameters (grade+1) (collarRadius lower positive bounded.le radius)
        (lowPhysicalRowKernel parameters length compact state row (collarRadius lower positive bounded.le radius))
        (curves.seven (grade+1) radius) := by
    exact conjugatedKernelAction_same parameters (grade+1) 0
      (collarRadius lower positive bounded.le radius) _ _ _ (fun mode => by rw [pow_zero,one_smul])
  rw [same 0,same 1,same 2]
  unfold balancedActualSource
  rw [collarRadius_literal lower positive bounded.le radius inside]

end Grad.OriginalCartesianTameEstimate
