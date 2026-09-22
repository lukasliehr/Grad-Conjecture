import AKI28LiteralHighCoordinateDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularReconstruction Grad.AnnularFourSource
open Grad.AnnularHighRadial Grad.AnnularHighTilt Grad.AnnularTiltedReference Grad.AnnularCurrentGreen
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.CircularHighRegularity

private theorem positiveScalar_weak_iff (lower : ℝ) (a ad : C(ℝ, ℝ))
    (positive : ∀ radius, 0 < a radius)
    (derivative : ∀ radius, HasDerivAt a (ad radius) radius)
    (value slope : CollarL2 (ComplexEuclidean 1) lower) :
    CollarWeakDerivative lower (collarScalar 1 lower a value)
      (collarScalar 1 lower ad value + collarScalar 1 lower a slope) ↔
      CollarWeakDerivative lower value slope := by
  let inverse : C(ℝ, ℝ) := ⟨fun radius => (a radius)⁻¹, a.continuous.inv₀ (fun radius => (positive radius).ne')⟩
  let inverseSlope : C(ℝ, ℝ) := ⟨fun radius => -(ad radius) / (a radius)^2,
    ad.continuous.neg.div (a.continuous.pow 2) (fun radius => pow_ne_zero 2 (positive radius).ne')⟩
  apply collarWeakDerivative_conjugation lower a ad inverse inverseSlope derivative
  · intro radius
    exact (derivative radius).inv (positive radius).ne'
  · intro radius
    exact inv_mul_cancel₀ (positive radius).ne'
  · intro radius
    change -(ad radius) / (a radius)^2 * a radius + (a radius)⁻¹ * ad radius = 0
    field_simp [(positive radius).ne']
    ring

 theorem rawHighPhase_positive (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (cell : ℤ) (radius : ℝ) : 0 < rawHighPhase parameters lower positive cell radius :=
  mul_pos (Real.rpow_pos_of_pos (highSmoothRadius_pos lower positive radius) _) (Real.exp_pos _)

/-- Actual r^(9/4) exp(-Phi) storage removal is reversible for weak rows. -/
theorem rawHighPhase_weak_iff (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (cell : ℤ) (value forcing : CollarL2 (ComplexEuclidean 1) lower) :
    CollarWeakDerivative lower (collarScalar 1 lower (rawHighPhase parameters lower positive cell) value)
      (collarScalar 1 lower (rawHighPhase parameters lower positive cell) forcing) ↔
      CollarWeakDerivative lower value
        (collarScalar 1 lower (annularTiltCurve parameters lower positive cell) value + forcing) := by
  have result := positiveScalar_weak_iff lower
    (rawHighPhase parameters lower positive cell) (rawHighPhaseSlope parameters lower positive cell)
    (rawHighPhase_positive parameters lower positive cell) (rawHighPhase_hasDerivAt parameters lower positive cell)
    value (collarScalar 1 lower (annularTiltCurve parameters lower positive cell) value + forcing)
  rw [map_add,rawHighPhase_compensated,neg_add_cancel_left] at result
  exact result

/-- The actual high ordinary flux weak row is equivalent to its raw physical
version, with the same full packet and original rV-rg coordinate. -/
theorem rawHighXPacket_weak_iff (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (packet : DivisionRow 3 lower) (mode : HighAnnularMode) :
    CollarWeakDerivative lower
      (collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
        (radialOrdinary 1 lower positive (highPhysicalOutput lower 0 packet mode)))
      (rawHighXPacketRHS parameters lower length positive packet mode) ↔
    CollarWeakDerivative lower
      (radialOrdinary 1 lower positive (highPhysicalOutput lower 0 packet mode))
      (physicalFluxOrdinarySlope parameters lower length positive packet mode) := by
  unfold rawHighXPacketRHS
  rw [rawHighPhase_weak_iff,physicalFluxOrdinarySlope_literal]
  abel_nf

end Grad.AnnularOriginalSmoothCore
