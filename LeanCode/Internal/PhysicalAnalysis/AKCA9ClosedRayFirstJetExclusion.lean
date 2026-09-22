import AKCA8SameRecoveredCorePointwiseBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.Cor18 Grad.NonlinearQuotientBounds

 def closedJetRay {dimension : ℕ} (field : ClosedJet dimension) (direction : Fin 2) (radius : ℝ) :
    ComplexEuclidean dimension := smoothClosedExtension field (radius • spatialBasis direction)

 theorem closedJetRay_continuous {dimension : ℕ} (field : ClosedJet dimension) (direction : Fin 2) :
    Continuous (closedJetRay field direction) :=
  (smoothClosedExtension_smooth field).continuous.comp (continuous_id.smul continuous_const)

 theorem closedJetRay_zero {dimension : ℕ} (field : ClosedJet dimension) (direction : Fin 2) :
    closedJetRay field direction 0 = originValue field := by
  change smoothClosedExtension field (0 • spatialBasis direction) = field.value originPoint
  rw [zero_smul]
  exact smoothClosedExtension_value field originPoint

 theorem closedJetRay_derivative {dimension : ℕ} (field : ClosedJet dimension) (direction : Fin 2) :
    HasDerivAt (closedJetRay field direction) (originPartial direction field) 0 := by
  have first : HasFDerivAt (smoothClosedExtension field) (fderiv ℝ (smoothClosedExtension field) 0) ((0 : ℝ) • spatialBasis direction) := by
    simpa only [zero_smul] using ((smoothClosedExtension_smooth field).differentiable (by simp)).differentiableAt.hasFDerivAt (x := (0 : SpatialPlane))
  have ray : HasDerivAt (fun radius : ℝ => radius • spatialBasis direction) (spatialBasis direction) 0 := by
    have derivative : HasDerivAt (fun radius : ℝ => radius • spatialBasis direction) ((1 : ℝ) • spatialBasis direction) 0 :=
      (hasDerivAt_id (0 : ℝ)).smul_const (spatialBasis direction)
    simpa only [one_smul] using derivative
  have derivative := first.comp_hasDerivAt 0 ray
  have value : fderiv ℝ (smoothClosedExtension field) 0 (spatialBasis direction) = originPartial direction field := by
    change spatialPartial direction (smoothClosedExtension field) originPoint.val = _
    rw [spatialPartial_eq_ordered,smoothClosedExtension_derivative]
    rfl
  exact value ▸ derivative

 theorem closedJet_criticalEnergy_zeroFirstJets {dimension : ℕ} (field : ClosedJet dimension)
    (finite : ∀ direction : Fin 2,
      (∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal
        (radius⁻¹ * (radius⁻¹ * ‖closedJetRay field direction radius‖) ^ 2)) < ⊤) :
    ZeroCartesianFirstJets field := by
  have zeros (direction : Fin 2) := logarithmicSlopeEnergy_zero_jet (closedJetRay field direction)
    (closedJetRay_continuous field direction).measurable (originPartial direction field)
    (closedJetRay_derivative field direction) (finite direction)
  rw [zeroCartesianFirstJets_iff]
  refine ⟨?_,fun direction => (zeros direction).2⟩
  exact (closedJetRay_zero field 0).symm.trans (zeros 0).1

end Grad.OriginalCoreRealization
