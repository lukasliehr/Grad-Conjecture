import AJW7HighRestrictionGrades
import AIV7SameInsertedGradeEquivalence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
open scoped Topology
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.AnnularVariational Grad.AnnularOmegaGraph Grad.AnnularGrades
open Grad.AnnularFluxTrace Grad.AnnularCrossMaps Grad.AnnularOriginalHigh Grad.AnnularHighTilt

def originalHighGradeDecode (lower length : ℝ) (positive : 0 < lower) (angular cell inserted : ℕ) :
    OriginalHighSpace lower length positive →L[ℂ] OriginalHighSpace lower length positive :=
  restrictionPairMap (annularEnergyDecode lower length positive angular cell inserted)
    (originalNuDecode lower positive angular cell inserted)

def weightedHighGradeDecode (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (angular cell inserted : ℕ) :
    CrossHighSpace lower length positive lengthPositive →L[ℂ] CrossHighSpace lower length positive lengthPositive :=
  restrictionPairMap (annularEnergyDecode lower length positive angular cell inserted)
    (annularOmegaGraphDecode lower length positive lengthPositive angular cell inserted)

theorem originalHighTilt_gradeDecode (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < length) (angular cell inserted : ℕ) (field : OriginalHighSpace lower length positive) :
    originalHighTiltEquivalence lower length positive bounded.le lengthPositive
      (originalHighGradeDecode lower length positive angular cell inserted field) =
    weightedHighGradeDecode lower length positive lengthPositive angular cell inserted
      (originalHighTiltEquivalence lower length positive bounded.le lengthPositive field) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext
  · exact originalEnergyTilt_decode lower length positive bounded angular cell inserted field.ofLp.1
  · exact originalFluxTilt_decode lower length positive bounded lengthPositive angular cell inserted field.ofLp.2

theorem highWeightedRestriction_gradeDecode (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper) (angular cell inserted : ℕ)
    (field : CrossHighSpace lower length lowerPositive lengthPositive) :
    highWeightedRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included
      (weightedHighGradeDecode lower length lowerPositive lengthPositive angular cell inserted field) =
    weightedHighGradeDecode upper length upperPositive lengthPositive angular cell inserted
      (highWeightedRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext
  · exact highEnergyRestriction_decode lower upper length lowerPositive upperPositive upperBounded included angular cell inserted field.ofLp.1
  · exact highOmegaRestriction_decode lower upper length lowerPositive upperPositive upperBounded lengthPositive included angular cell inserted field.ofLp.2

/-- The retained map commutes with the literal original three-parameter graph decoder. -/
theorem originalHighRestriction_gradeDecode (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper) (angular cell inserted : ℕ)
    (field : OriginalHighSpace lower length lowerPositive) :
    originalHighRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included
      (originalHighGradeDecode lower length lowerPositive angular cell inserted field) =
    originalHighGradeDecode upper length upperPositive angular cell inserted
      (originalHighRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field) := by
  apply (originalHighTiltEquivalence upper length upperPositive upperBounded.le lengthPositive).injective
  exact (originalHighRestriction_weighted lower upper length lowerPositive upperPositive upperBounded lengthPositive included
    (originalHighGradeDecode lower length lowerPositive angular cell inserted field)).trans
    ((congrArg (highWeightedRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included)
      (originalHighTilt_gradeDecode lower length lowerPositive (included.trans_lt upperBounded) lengthPositive angular cell inserted field)).trans
      ((highWeightedRestriction_gradeDecode lower upper length lowerPositive upperPositive upperBounded lengthPositive included angular cell inserted
        (originalHighTiltEquivalence lower length lowerPositive (included.trans upperBounded.le) lengthPositive field)).trans
        ((congrArg (weightedHighGradeDecode upper length upperPositive lengthPositive angular cell inserted)
          (originalHighRestriction_weighted lower upper length lowerPositive upperPositive upperBounded lengthPositive included field).symm).trans
          (originalHighTilt_gradeDecode upper length upperPositive upperBounded lengthPositive angular cell inserted
            (originalHighRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field)).symm)))

/-- Every genuine original weighted witness restricts to a weighted witness of the same grade. -/
theorem originalHighRestriction_gradeRange (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper) (angular cell inserted : ℕ)
    (field : OriginalHighSpace lower length lowerPositive)
    (grade : field ∈ LinearMap.range (originalHighGradeDecode lower length lowerPositive angular cell inserted).toLinearMap) :
    originalHighRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field ∈
      LinearMap.range (originalHighGradeDecode upper length upperPositive angular cell inserted).toLinearMap := by
  obtain ⟨weighted, rfl⟩ := grade
  exact ⟨originalHighRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included weighted,
    (originalHighRestriction_gradeDecode lower upper length lowerPositive upperPositive upperBounded lengthPositive included angular cell inserted weighted).symm⟩

end Grad.AnnularRestriction
