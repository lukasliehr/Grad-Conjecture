import AJO2OriginalPhysicalBalancingCurves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowClassical
open Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularRegularity
open Grad.AnnularFluxTrace Grad.CircularHighRegularity Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.AnnularReconstruction

private theorem unbalanceSlope {E : Type*} [AddCommGroup E] [Module ℝ E]
    (factor logarithmic : ℝ) (nonzero : factor ≠ 0) (value derivative : E) :
    factor⁻¹ • (factor • derivative + (factor * logarithmic) • value) +
      (-(factor * logarithmic) / factor ^ 2) • (factor • value) = derivative := by
  rw [add_comm]
  have cancel : (-(factor * logarithmic) / factor ^ 2) * factor + factor⁻¹ * (factor * logarithmic) = 0 := by
    field_simp [nonzero]
    ring
  simp only [smul_add, smul_smul, inv_mul_cancel₀ nonzero, one_smul]
  rw [add_comm derivative, ← add_assoc, ← add_smul, cancel, zero_smul, zero_add]

/-- The genuine weak low graph differentiates to a continuous candidate
physical RHS when that RHS equals the original encoded slope almost everywhere.
This is the inverse of the actual balancing factor, not a reference ODE. -/
theorem lowPhysicalSection_derivative (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : lowEnergyGraph lower length positive)
    (index : LowAnnularIndex) (rhs : C(ℝ, ComplexEuclidean 1))
    (same : lowEnergyDerivative lower length positive index field.val =ᵐ[volume.restrict (Icc lower 1)]
      lowEncodedSlopeCurve parameters lower length positive bounded field index rhs)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt
      (radialSectionExtension 1 lower bounded.le (lowPhysicalSection parameters lower length positive bounded field index))
      (rhs radius) (Icc lower 1) radius := by
  have normalized := lowEnergySection_derivative lower length positive bounded field index
    (lowEncodedSlopeCurve parameters lower length positive bounded field index rhs) same radius inside
  have factorPositive := lowPhysicalFactor_pos parameters length radius (positive.trans_le inside.1) index
  have inverse := (lowPhysicalFactor_hasDerivAt parameters length radius index.2
    (positive.trans_le inside.1) index.1).inv factorPositive.ne'
  have differentiated := inverse.hasDerivWithinAt.smul normalized
  have energyValue : radialSectionExtension 1 lower bounded.le (lowEnergySection lower length positive bounded field index) radius =
      lowPhysicalFactor parameters length radius index • lowPhysicalSection parameters lower length positive bounded field index ⟨radius, inside⟩ :=
    (lowSectionExtension_eval lower bounded.le _ radius inside).trans
      (lowPhysicalSection_encode parameters lower length positive bounded field index ⟨radius, inside⟩).symm
  rw [energyValue, lowEncodedSlopeCurve_actual parameters lower length positive bounded field index rhs radius inside] at differentiated
  have cleaned : HasDerivWithinAt
      (fun point => (lowPhysicalFactor parameters length point index)⁻¹ •
        radialSectionExtension 1 lower bounded.le (lowEnergySection lower length positive bounded field index) point)
      (rhs radius) (Icc lower 1) radius := by
    change HasDerivWithinAt
      (fun point => (lowPhysicalFactor parameters length point index)⁻¹ •
        radialSectionExtension 1 lower bounded.le (lowEnergySection lower length positive bounded field index) point)
      ((lowPhysicalFactor parameters length radius index)⁻¹ •
        (lowPhysicalFactor parameters length radius index • rhs radius +
          (lowPhysicalFactor parameters length radius index * lowBalancingLogSlope parameters length radius index.2 index.1) •
            lowPhysicalSection parameters lower length positive bounded field index ⟨radius, inside⟩) +
        (-(lowPhysicalFactor parameters length radius index * lowBalancingLogSlope parameters length radius index.2 index.1) /
          lowPhysicalFactor parameters length radius index ^ 2) •
          (lowPhysicalFactor parameters length radius index • lowPhysicalSection parameters lower length positive bounded field index ⟨radius, inside⟩))
      (Icc lower 1) radius at differentiated
    rw [unbalanceSlope _ _ factorPositive.ne'] at differentiated
    exact differentiated
  have equality (point : ℝ) (member : point ∈ Icc lower 1) :
      radialSectionExtension 1 lower bounded.le (lowPhysicalSection parameters lower length positive bounded field index) point =
        (lowPhysicalFactor parameters length point index)⁻¹ •
          radialSectionExtension 1 lower bounded.le (lowEnergySection lower length positive bounded field index) point := by
    rw [lowSectionExtension_eval lower bounded.le _ point member,
      lowSectionExtension_eval lower bounded.le _ point member]
    dsimp only [lowPhysicalSection, radialSectionScalar]
    change lowPhysicalInverseCurve parameters lower length positive index point •
      lowEnergySection lower length positive bounded field index ⟨point, member⟩ =
      (lowPhysicalFactor parameters length point index)⁻¹ •
        lowEnergySection lower length positive bounded field index ⟨point, member⟩
    rw [lowPhysicalInverseCurve_original parameters lower length positive index point member]
  exact cleaned.congr equality (equality radius inside)

end Grad.AnnularLowClassical
