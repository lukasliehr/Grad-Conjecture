import AJZ2FullFourierSourceRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularSourceGraph

theorem collarL2Restriction_radialSqrt (dimension : ℕ) (lower upper : ℝ)
    (included : lower ≤ upper) (field : CollarL2 (ComplexEuclidean dimension) lower) :
    collarL2Restriction dimension lower upper included (radialSqrtMap dimension lower field) =
      radialSqrtMap dimension upper (collarL2Restriction dimension lower upper included field) := by
  apply Lp.ext
  filter_upwards [collarL2Restriction_ae dimension lower upper included (radialSqrtMap dimension lower field),
    (radialSqrtMap_ae dimension lower field).filter_mono (ae_mono (collarMeasure_le lower upper included)),
    radialSqrtMap_ae dimension upper (collarL2Restriction dimension lower upper included field),
    collarL2Restriction_ae dimension lower upper included field] with radius restriction source target actual
  rw [restriction, source, target, actual]

theorem sourceRadialRestriction_ordinary (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (positiveLower : 0 < lower) (positiveUpper : 0 < upper) (bounded : upper ≤ 1)
    (field : WeightedRadialH1 dimension lower) (slot : Fin 2) :
    collarH1Coordinate (ComplexEuclidean dimension) upper slot
        (weightedToOrdinary dimension upper positiveUpper bounded
          (sourceRadialRestriction dimension lower upper included field)) =
      collarL2Restriction dimension lower upper included
        (collarH1Coordinate (ComplexEuclidean dimension) lower slot
          (weightedToOrdinary dimension lower positiveLower (included.trans bounded) field)) := by
  apply radialSqrtMap_injective dimension upper positiveUpper
  rw [← weightedRadialCoordinate_eq_sqrt, sourceRadialRestriction_coordinate,
    ← collarL2Restriction_radialSqrt, ← weightedRadialCoordinate_eq_sqrt]

/-- Both decoded original conjugated coordinates commute with restriction.
The second remains the derivative of the first on the genuine source graph. -/
theorem sourceGraphRestriction_conjugated (parameters : PhaseParameters) (dimension : ℕ)
    (lower upper : ℝ) (included : lower ≤ upper) (positiveLower : 0 < lower)
    (positiveUpper : 0 < upper) (bounded : upper ≤ 1) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade)
    (mode : ℤ × ℤ) (slot : Fin 2) :
    totalConjugatedCoordinate parameters dimension upper positiveUpper bounded angular cell grade
        (sourceGraphRestriction parameters dimension lower upper included angular cell grade field) mode slot =
      collarL2Restriction dimension lower upper included
        (totalConjugatedCoordinate parameters dimension lower positiveLower (included.trans bounded)
          angular cell grade field mode slot) := by
  unfold totalConjugatedCoordinate totalConjugatedMode
  rw [sourceGraphRestriction_apply, map_smul, map_smul,
    sourceRadialRestriction_ordinary dimension lower upper included positiveLower positiveUpper bounded,
    (collarL2Restriction dimension lower upper included).map_smul_of_tower]

theorem sourceGraphRestriction_physical (parameters : PhaseParameters) (dimension : ℕ)
    (lower upper : ℝ) (included : lower ≤ upper) (positiveLower : 0 < lower)
    (positiveUpper : 0 < upper) (bounded : upper ≤ 1) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade) :
    ∀ᵐ radius ∂volume.restrict (Icc upper 1), ∀ mode : ℤ × ℤ,
      totalSourceCoefficient parameters dimension upper positiveUpper bounded angular cell grade
          (sourceGraphRestriction parameters dimension lower upper included angular cell grade field) mode radius =
        totalSourceCoefficient parameters dimension lower positiveLower (included.trans bounded)
          angular cell grade field mode radius := by
  rw [ae_all_iff]
  intro mode
  filter_upwards [collarL2Restriction_ae dimension lower upper included
    (totalConjugatedCoordinate parameters dimension lower positiveLower (included.trans bounded)
      angular cell grade field mode 0)] with radius actual
  unfold totalSourceCoefficient
  rw [sourceGraphRestriction_conjugated parameters dimension lower upper included positiveLower positiveUpper bounded,
    actual]

theorem sourceGraphRestriction_genuineWeak (parameters : PhaseParameters) (dimension : ℕ)
    (lower upper : ℝ) (included : lower ≤ upper) (positiveLower : 0 < lower)
    (positiveUpper : 0 < upper) (bounded : upper < 1) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade) (mode : ℤ × ℤ) :
    CollarWeakDerivative upper
      (collarL2Restriction dimension lower upper included
        (totalConjugatedCoordinate parameters dimension lower positiveLower (included.trans bounded.le)
          angular cell grade field mode 0))
      (collarL2Restriction dimension lower upper included
        (totalConjugatedCoordinate parameters dimension lower positiveLower (included.trans bounded.le)
          angular cell grade field mode 1)) :=
  collarWeakDerivative_restrict dimension lower upper included positiveUpper bounded _ _
    (totalConjugatedCoordinate_weak parameters dimension lower positiveLower (included.trans bounded.le)
      angular cell grade field mode)

end Grad.AnnularRestriction
