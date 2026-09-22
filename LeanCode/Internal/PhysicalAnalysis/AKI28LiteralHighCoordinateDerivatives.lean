import AKI27ArbitraryOriginalLowPDE

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularFullGraph
open Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.AnnularHighRadial
open Grad.AnnularLowClassical Grad.AnnularCurrentEnergy Grad.AnnularVariational

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (data : OriginalStrongCarrier parameters lower 0 0) (candidate : OriginalCoupledSpace lower length positive)
    (tuple : OriginalSmoothTuple parameters lower)
    (represented : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state tuple
      (originalFiveBlockObservation parameters lower length positive (data,candidate)))

private abbrev highCandidate := originalCoupledEquivalence parameters lower length positive bounded.le lengthPositive candidate
include represented

/-- Genuine derivative of the arbitrary candidate's SAME raw high xi. -/
theorem OriginalTupleObservation.highXi_derivative (mode : HighAnnularMode)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (radialSectionExtension 1 lower bounded.le
      (rawHighXiSection parameters lower length positive bounded
        (highCandidate parameters length lower positive bounded lengthPositive candidate).ofLp.1.ofLp.1 mode))
      (originalTupleSlopeCurve parameters lower bounded tuple 1 mode.val radius) (Icc lower 1) radius := by
  have same (location : ℝ) (member : location ∈ Icc lower 1) :
      radialSectionExtension 1 lower bounded.le
        (rawHighXiSection parameters lower length positive bounded
          (highCandidate parameters length lower positive bounded lengthPositive candidate).ofLp.1.ofLp.1 mode) location =
        originalPhysicalCoefficient (tuple.val 1) location mode.val := by
    rw [lowSectionExtension_eval lower bounded.le _ location member]
    exact ((represented.scalar ⟨location,member⟩ mode.val).trans
      (sameCoupledXiCoefficient_high parameters lower length positive bounded lengthPositive
        (highCandidate parameters length lower positive bounded lengthPositive candidate) mode ⟨location,member⟩)).symm
  exact (originalTuple_coefficient_derivative parameters lower bounded tuple 1 mode.val radius inside).congr same (same radius inside)

/-- Genuine derivative of the arbitrary candidate's SAME raw high X=Rp. -/
theorem OriginalTupleObservation.highX_derivative (mode : HighAnnularMode)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (radialSectionExtension 1 lower bounded.le
      (rawHighXSection parameters lower length positive bounded lengthPositive
        (highCandidate parameters length lower positive bounded lengthPositive candidate).ofLp.1.ofLp.2 mode))
      (frequencyNumerator (some false) mode.val • originalTupleSlopeCurve parameters lower bounded tuple 0 mode.val radius) (Icc lower 1) radius := by
  have same (location : ℝ) (member : location ∈ Icc lower 1) :
      radialSectionExtension 1 lower bounded.le
        (rawHighXSection parameters lower length positive bounded lengthPositive
          (highCandidate parameters length lower positive bounded lengthPositive candidate).ofLp.1.ofLp.2 mode) location =
        frequencyNumerator (some false) mode.val • originalPhysicalCoefficient (tuple.val 0) location mode.val := by
    rw [lowSectionExtension_eval lower bounded.le _ location member]
    exact ((represented.pressure_R parameters length compact lower positive bounded lengthPositive state data candidate tuple ⟨location,member⟩ mode.val).trans
      (sameCoupledXCoefficient_high parameters lower length positive bounded lengthPositive
        (highCandidate parameters length lower positive bounded lengthPositive candidate) mode ⟨location,member⟩)).symm
  exact ((originalTuple_coefficient_derivative parameters lower bounded tuple 0 mode.val radius inside).const_smul
    (frequencyNumerator (some false) mode.val)).congr same (same radius inside)

end Grad.AnnularOriginalSmoothCore
