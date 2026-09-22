import AKDX9CanonicalPolarTensorEnergy
import AKBZ6OriginalPureEndpointNorms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.OriginalCollarNorm
open Grad.Constraints Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger

theorem polarJetSquaredDensity_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : ℝ×ℝ→E) {low high : ℕ} (ordered : low≤high) (point : ℝ×ℝ) :
    polarJetSquaredDensity field low point≤polarJetSquaredDensity field high point := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun _ _ _ => sq_nonneg _)

/-- A single constant controls the complete original ordinary mass row,
including all lower derivatives, by the fixed-collar polar energy. -/
theorem fixedCutoff_massRow_energy (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (cutoff : SpatialPlane→ℝ) (cutoffSmooth : ContDiff ℝ ∞ cutoff)
    (vanishes : ∀ point,‖point‖<2*lower → cutoff point=0) (grade : ℕ) :
    ∃ constant : ℝ,0≤constant ∧ ∀ dimension (field : SpatialPlane→ComplexEuclidean dimension)
      (smooth : ContDiff ℝ ∞ field),
      ‖apMassRow 1 grade (globalClosedJet (fun point => cutoff point • field point)
        (cutoffSmooth.smul smooth))‖^2≤constant*fixedCollarIntegral lower
          (polarJetSquaredDensity (field ∘ collarPlane) grade) := by
  let choice := fun index : DerivativeIndex grade =>
    fixedCutoff_cartesian_energy lower positive bounded cutoff cutoffSmooth vanishes (derivativeMultiIndex index)
  let constants := fun index : DerivativeIndex grade => (choice index).choose
  have nonnegative (index : DerivativeIndex grade) : 0≤constants index := (choice index).choose_spec.1
  refine ⟨∑ index,constants index,Finset.sum_nonneg (fun index _ => nonnegative index),?_⟩
  intro dimension field smooth
  rw [PiLp.norm_sq_eq_of_L2,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index _
  rw [apMassRow_coordinate_norm 1 zero_le_one,one_pow,one_mul]
  have bound := (choice index).choose_spec.2 dimension field smooth
  have ordered : cartesianOrder (derivativeMultiIndex index)≤grade := index.property
  have comparison := fixedCollarIntegral_mono lower bounded
    (polarJetSquaredDensity (field ∘ collarPlane) (cartesianOrder (derivativeMultiIndex index)))
    (polarJetSquaredDensity (field ∘ collarPlane) grade)
    (polarJetSquaredDensity_continuous _ (smooth.comp collarPlane_smooth) _)
    (polarJetSquaredDensity_continuous _ (smooth.comp collarPlane_smooth) _)
    (fun point _ => polarJetSquaredDensity_mono _ ordered point)
  exact bound.trans (mul_le_mul_of_nonneg_left comparison (nonnegative index))

end Grad.OriginalCollarNorm
