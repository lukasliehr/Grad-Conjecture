import AKI23LiteralResidualRawEquations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularLowEnergy Grad.AnnularLowReference
open Grad.AnnularLowClassical Grad.AnnularReconstruction Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (field : lowEnergyGraph lower length positive)

/-- Reverse the original physical balancing without altering mu or rho. -/
theorem lowEnergySection_derivative_of_physical (index : LowAnnularIndex)
    (rhs : C(ℝ, ComplexEuclidean 1))
    (derivative : ∀ radius ∈ Icc lower 1,
      HasDerivWithinAt (radialSectionExtension 1 lower bounded.le
        (lowPhysicalSection parameters lower length positive bounded field index)) (rhs radius) (Icc lower 1) radius)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (radialSectionExtension 1 lower bounded.le
      (lowEnergySection lower length positive bounded field index))
      (lowEncodedSlopeCurve parameters lower length positive bounded field index rhs radius) (Icc lower 1) radius := by
  have factor := lowPhysicalFactor_hasDerivAt parameters length radius index.2 (positive.trans_le inside.1) index.1
  have product := factor.hasDerivWithinAt.smul (derivative radius inside)
  have equality (location : ℝ) (member : location ∈ Icc lower 1) :
      radialSectionExtension 1 lower bounded.le (lowEnergySection lower length positive bounded field index) location =
        lowPhysicalFactor parameters length location index •
          radialSectionExtension 1 lower bounded.le (lowPhysicalSection parameters lower length positive bounded field index) location := by
    rw [lowSectionExtension_eval lower bounded.le _ location member,
      lowSectionExtension_eval lower bounded.le _ location member]
    exact (lowPhysicalSection_encode parameters lower length positive bounded field index ⟨location,member⟩).symm
  rw [lowEncodedSlopeCurve_actual parameters lower length positive bounded field index rhs radius inside]
  have sameValue := lowSectionExtension_eval lower bounded.le
    (lowPhysicalSection parameters lower length positive bounded field index) radius inside
  rw [sameValue] at product
  exact product.congr equality (equality radius inside)

/-- A classical physical row fixes the genuine stored low derivative.
The proof uses weak derivative uniqueness on the candidate's actual graph. -/
theorem lowStoredRow_of_physical (target : LowEnergyBulk lower)
    (rhs : LowAnnularIndex → C(ℝ, ComplexEuclidean 1))
    (derivative : ∀ index radius, radius ∈ Icc lower 1 →
      HasDerivWithinAt (radialSectionExtension 1 lower bounded.le
        (lowPhysicalSection parameters lower length positive bounded field index)) (rhs index radius) (Icc lower 1) radius)
    (encoded : ∀ index,
      collarScalar 1 lower (lowMuCurve lower length positive index.2.val.2)
        (collarScalar 1 lower (lowStorageInverse lower positive) (target index)) =ᵐ[volume.restrict (Icc lower 1)]
          lowEncodedSlopeCurve parameters lower length positive bounded field index (rhs index)) :
    field.val 1 = target := by
  apply lp.ext
  funext index
  apply collarScalar_injective_of_pos lower (lowStorageInverse lower positive)
    (lowPowerCurve_pos lower (7 / 4 : ℝ) positive)
  apply collarScalar_injective_of_pos lower (lowMuCurve lower length positive index.2.val.2)
    (lowMuCurve_pos lower length positive index.2.val.2)
  apply collarWeakDerivative_unique lower (field.property index)
  apply collarWeakDerivative_of_representatives lower bounded.le _ _
    (radialSectionExtension 1 lower bounded.le (lowEnergySection lower length positive bounded field index))
    (lowEncodedSlopeCurve parameters lower length positive bounded field index (rhs index))
  · rw [← lowEnergySection_bulk lower length positive bounded field index]
    filter_upwards [radialSectionL2_ae 1 lower positive bounded.le
      (lowEnergySection lower length positive bounded field index)] with radius same
    exact same.symm
  · exact encoded index
  · exact lowEnergySection_derivative_of_physical parameters lower length positive bounded field index (rhs index) (derivative index)

end Grad.AnnularOriginalSmoothCore
