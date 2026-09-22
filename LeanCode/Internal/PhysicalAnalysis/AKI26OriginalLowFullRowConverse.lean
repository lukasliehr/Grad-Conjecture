import AKI25LiteralTupleDerivativeCurves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularLowEnergy Grad.AnnularLowReference
open Grad.AnnularLowClassical Grad.AnnularReconstruction Grad.AnnularCurrentLow Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.CircularHighRegularity

/-- The proposed full stored low row has precisely the balancing derivative
of the original raw RHS, independently of the candidate's equation. -/
theorem lowFullRowRHS_encoded_ae (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : lowEnergyGraph lower length positive) (first cell angular : DivisionRow 1 lower)
    (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      collarScalar 1 lower (lowMuCurve lower length positive index.2.val.2)
        (collarScalar 1 lower (lowStorageInverse lower positive)
          (lowFullRowRHS parameters lower length positive lengthPositive (field.val 0) first cell angular index)) radius =
        lowPhysicalFactor parameters length radius index • lowPhysicalRawSlope parameters lower length positive bounded field first cell angular index radius +
        (lowPhysicalFactor parameters length radius index * lowBalancingLogSlope parameters length radius index.2 index.1) •
          radialSectionExtension 1 lower bounded.le (lowPhysicalSection parameters lower length positive bounded field index) radius := by
  let target := lowFullRowRHS parameters lower length positive lengthPositive (field.val 0) first cell angular index
  filter_upwards [collarScalar_ae 1 lower (lowMuCurve lower length positive index.2.val.2)
      (collarScalar 1 lower (lowStorageInverse lower positive) target),
    collarScalar_ae 1 lower (lowStorageInverse lower positive) target,
    lowFullRowRHS_ae parameters lower length positive lengthPositive (field.val 0) first cell angular index,
    lowStoredValue_section_ae lower length positive bounded field index,
    ae_restrict_mem measurableSet_Icc] with radius outer inner rows stored inside
  have decoded : collarScalar 1 lower (lowMuCurve lower length positive index.2.val.2)
      (collarScalar 1 lower (lowStorageInverse lower positive) target) radius =
      lowMu length radius index.2.val.2 • (lowStorageInverse lower positive radius • target radius) := by
    rw [outer,inner]
    change lowMu length (max lower radius) index.2.val.2 • _ = _
    rw [max_eq_right inside.1]
  have value : lowStorageInverse lower positive radius • field.val 0 index radius =
      lowPhysicalFactor parameters length radius index •
        radialSectionExtension 1 lower bounded.le (lowPhysicalSection parameters lower length positive bounded field index) radius := by
    rw [stored, smul_smul, mul_comm, lowStorage_inverse, one_smul,
      lowSectionExtension_eval lower bounded.le _ radius inside,
      lowSectionExtension_eval lower bounded.le _ radius inside]
    exact (lowPhysicalSection_encode parameters lower length positive bounded field index ⟨radius, inside⟩).symm
  rw [decoded, rows]
  rcases index with ⟨entry, mode⟩
  fin_cases entry
  · norm_num only [lowPhysicalRawSlope, Fin.ext_iff, Fin.val_zero, Fin.val_one, if_true, if_false, smul_zero, add_zero, zero_add]
    simp only [smul_add, smul_comm (lowStorageInverse lower positive radius)]
    rw [value, lowRhoPhysicalCoefficient_storage parameters lower positive first radius mode.val]
    simpa [lowPhysicalFactor, lowBalancingLogSlope, smul_add] using
      lowXiBalance (lowMu length radius mode.val.2) (annularPhaseSlope parameters mode.val.2 radius)
        (lowMuLogSlope length radius mode.val.2) (lowAmplitude length parameters.gamma mode)
        (Real.exp (radialPhase parameters radius mode.val.2))
        (lowMu_pos length radius mode.val.2 (positive.trans_le inside.1)).ne'
        (radialSectionExtension 1 lower bounded.le (lowPhysicalSection parameters lower length positive bounded field (0, mode)) radius)
        (lowRhoPhysicalCoefficient parameters lower positive first radius mode.val)
  · norm_num only [lowPhysicalRawSlope, Fin.ext_iff, Fin.val_zero, Fin.val_one, if_true, if_false, smul_zero, add_zero, zero_add]
    simp only [smul_add, smul_comm (lowStorageInverse lower positive radius)]
    rw [value, lowRhoPhysicalCoefficient_storage parameters lower positive cell radius mode.val,
      lowRhoPhysicalCoefficient_storage parameters lower positive angular radius mode.val]
    norm_num only [lowPhysicalFactor, lowBalancingLogSlope, Fin.ext_iff, Fin.val_zero, Fin.val_one, if_true, if_false, mul_one, add_zero]
    simp only [smul_comm (-Complex.I)]
    with_unfolding_all
      simpa [neg_div, one_div, sub_eq_add_neg, smul_add] using
      lowXBalance (lowMu length radius mode.val.2) (annularPhaseSlope parameters mode.val.2 radius)
        radius⁻¹ ((mode.val.2 : ℝ) / length) ((mode.val.1 : ℝ) * radius⁻¹)
        (Real.exp (radialPhase parameters radius mode.val.2))
        (lowMu_pos length radius mode.val.2 (positive.trans_le inside.1)).ne'
        (radialSectionExtension 1 lower bounded.le (lowPhysicalSection parameters lower length positive bounded field (1, mode)) radius)
        ((-Complex.I) • lowRhoPhysicalCoefficient parameters lower positive cell radius mode.val)
        ((-Complex.I) • lowRhoPhysicalCoefficient parameters lower positive angular radius mode.val)

/-- Full reverse original low row, using actual classical raw equations and
weak graph uniqueness; no stored derivative premise is required. -/
theorem lowFullRows_of_rawClassical (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : lowEnergyGraph lower length positive) (first cell angular : DivisionRow 1 lower)
    (rhs : LowAnnularIndex → C(ℝ, ComplexEuclidean 1))
    (derivative : ∀ index radius, radius ∈ Icc lower 1 →
      HasDerivWithinAt (radialSectionExtension 1 lower bounded.le
        (lowPhysicalSection parameters lower length positive bounded field index)) (rhs index radius) (Icc lower 1) radius)
    (actual : ∀ index, rhs index =ᵐ[volume.restrict (Icc lower 1)]
      lowPhysicalRawSlope parameters lower length positive bounded field first cell angular index) :
    field.val 1 = lowFullRowRHS parameters lower length positive lengthPositive (field.val 0) first cell angular := by
  apply lowStoredRow_of_physical parameters lower length positive bounded field _ rhs derivative
  intro index
  filter_upwards [lowFullRowRHS_encoded_ae parameters lower length positive bounded lengthPositive field first cell angular index,
    actual index, ae_restrict_mem measurableSet_Icc] with radius encoded actual inside
  rw [lowEncodedSlopeCurve_actual parameters lower length positive bounded field index (rhs index) radius inside,
    actual, ← lowSectionExtension_eval lower bounded.le _ radius inside]
  exact encoded

end Grad.AnnularOriginalSmoothCore
