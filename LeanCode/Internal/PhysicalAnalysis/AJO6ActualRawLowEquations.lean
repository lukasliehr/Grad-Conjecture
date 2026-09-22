import AJO5OriginalRhoCancellation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowClassical
open Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularRegularity
open Grad.AnnularFluxTrace Grad.CircularHighRegularity Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.AnnularReconstruction Grad.AnnularCurrentLow Grad.PhaseAlgebra

/-- Original projected xi equation and x equation. The angular row is rV-rg,
so its negative imaginary multiplier retains the original positive Rg term. -/
def lowPhysicalRawSlope (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : lowEnergyGraph lower length positive)
    (first cell angular : DivisionRow 1 lower) (index : LowAnnularIndex) (radius : ℝ) : ComplexEuclidean 1 :=
  if index.1 = 0 then lowRhoPhysicalCoefficient parameters lower positive first radius index.2.val
  else (-radius⁻¹) • radialSectionExtension 1 lower bounded.le
      (lowPhysicalSection parameters lower length positive bounded field index) radius +
    (-Complex.I) • (((index.2.val.2 : ℝ) / length) • lowRhoPhysicalCoefficient parameters lower positive cell radius index.2.val) +
    (-Complex.I) • (((index.2.val.1 : ℝ) * radius⁻¹) • lowRhoPhysicalCoefficient parameters lower positive angular radius index.2.val)

theorem lowEnergyDerivative_raw_ae (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : lowEnergyGraph lower length positive) (first cell angular : DivisionRow 1 lower)
    (equation : field.val 1 = lowFullRowRHS parameters lower length positive lengthPositive (field.val 0) first cell angular)
    (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowEnergyDerivative lower length positive index field.val radius =
        lowPhysicalFactor parameters length radius index • lowPhysicalRawSlope parameters lower length positive bounded field first cell angular index radius +
        (lowPhysicalFactor parameters length radius index * lowBalancingLogSlope parameters length radius index.2 index.1) •
          radialSectionExtension 1 lower bounded.le (lowPhysicalSection parameters lower length positive bounded field index) radius := by
  filter_upwards [lowEnergyDerivative_fullRows_ae parameters lower length positive lengthPositive field first cell angular equation index,
    lowFullRowRHS_ae parameters lower length positive lengthPositive (field.val 0) first cell angular index,
    lowStoredValue_section_ae lower length positive bounded field index,
    ae_restrict_mem measurableSet_Icc] with radius derivative rows stored inside
  have value : lowStorageInverse lower positive radius • field.val 0 index radius =
      lowPhysicalFactor parameters length radius index •
        radialSectionExtension 1 lower bounded.le (lowPhysicalSection parameters lower length positive bounded field index) radius := by
    rw [stored, smul_smul, mul_comm, lowStorage_inverse, one_smul,
      lowSectionExtension_eval lower bounded.le _ radius inside,
      lowSectionExtension_eval lower bounded.le _ radius inside]
    exact (lowPhysicalSection_encode parameters lower length positive bounded field index ⟨radius, inside⟩).symm
  rw [derivative, rows]
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

/-- Genuine classical raw-coordinate PDE from the full stored equation and
an explicitly continuous representative of its literal physical RHS. -/
theorem lowPhysicalSection_fullRows_derivative (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : lowEnergyGraph lower length positive) (first cell angular : DivisionRow 1 lower)
    (equation : field.val 1 = lowFullRowRHS parameters lower length positive lengthPositive (field.val 0) first cell angular)
    (index : LowAnnularIndex) (rhs : C(ℝ, ComplexEuclidean 1))
    (actual : rhs =ᵐ[volume.restrict (Icc lower 1)] lowPhysicalRawSlope parameters lower length positive bounded field first cell angular index)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (radialSectionExtension 1 lower bounded.le
      (lowPhysicalSection parameters lower length positive bounded field index)) (rhs radius) (Icc lower 1) radius := by
  apply lowPhysicalSection_derivative parameters lower length positive bounded field index rhs
  filter_upwards [lowEnergyDerivative_raw_ae parameters lower length positive bounded lengthPositive field first cell angular equation index,
    actual, ae_restrict_mem measurableSet_Icc] with point derivative actual member
  rw [lowEncodedSlopeCurve_actual parameters lower length positive bounded field index rhs point member,
    ← lowSectionExtension_eval lower bounded.le _ point member, actual]
  exact derivative
  exact inside

end Grad.AnnularLowClassical
