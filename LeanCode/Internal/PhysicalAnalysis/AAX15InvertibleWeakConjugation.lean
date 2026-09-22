import AAX14ActualPhysicalResidual

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFourSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.AnnularGrades Grad.AnnularConverse
open Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

private theorem inverseSlopePoint {E : Type*} [AddCommGroup E] [Module ℝ E]
    (a ad b bd : ℝ) (v d : E) (inverse : b * a = 1) (cancel : bd * a + b * ad = 0) :
    bd • (a • v) + b • (ad • v + a • d) = d := by
  rw [smul_add, smul_smul, smul_smul, smul_smul, ← add_assoc, ← add_smul, cancel,
    inverse, zero_smul, one_smul, zero_add]

theorem collarScalar_inverse_apply (lower : ℝ) (a b : C(ℝ, ℝ))
    (inverse : ∀ radius, b radius * a radius = 1) (v : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower b (collarScalar 1 lower a v) = v := by
  rw [collarScalar_mul_apply]
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower (b * a) v] with radius equality
  rw [equality]
  change (b radius * a radius) • v radius = v radius
  rw [inverse, one_smul]

theorem collarScalar_inverse_slope (lower : ℝ) (a ad b bd : C(ℝ, ℝ))
    (inverse : ∀ radius, b radius * a radius = 1)
    (cancel : ∀ radius, bd radius * a radius + b radius * ad radius = 0)
    (v d : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower bd (collarScalar 1 lower a v) +
      collarScalar 1 lower b (collarScalar 1 lower ad v + collarScalar 1 lower a d) = d := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (collarScalar 1 lower bd (collarScalar 1 lower a v))
      (collarScalar 1 lower b (collarScalar 1 lower ad v + collarScalar 1 lower a d)),
    collarScalar_ae 1 lower bd (collarScalar 1 lower a v),
    collarScalar_ae 1 lower a v,
    collarScalar_ae 1 lower b (collarScalar 1 lower ad v + collarScalar 1 lower a d),
    Lp.coeFn_add (collarScalar 1 lower ad v) (collarScalar 1 lower a d),
    collarScalar_ae 1 lower ad v, collarScalar_ae 1 lower a d]
    with radius sum outer1 inner1 outer2 sum2 inner2 inner3
  rw [sum, Pi.add_apply, outer1, inner1, outer2, sum2, Pi.add_apply, inner2, inner3]
  exact inverseSlopePoint (a radius) (ad radius) (b radius) (bd radius) (v radius) (d radius)
    (inverse radius) (cancel radius)

/-- Reversible weak product rule; multiplication by the physical phase
neither assumes nor loses radial derivative membership. -/
theorem collarWeakDerivative_conjugation (lower : ℝ) (a ad b bd : C(ℝ, ℝ))
    (da : ∀ radius, HasDerivAt a (ad radius) radius)
    (db : ∀ radius, HasDerivAt b (bd radius) radius)
    (inverse : ∀ radius, b radius * a radius = 1)
    (cancel : ∀ radius, bd radius * a radius + b radius * ad radius = 0)
    (v d : CollarL2 (ComplexEuclidean 1) lower) :
    CollarWeakDerivative lower (collarScalar 1 lower a v)
      (collarScalar 1 lower ad v + collarScalar 1 lower a d) ↔ CollarWeakDerivative lower v d := by
  constructor
  · intro weak
    have result := collarWeakDerivative_scalar lower b bd db _ _ weak
    exact (congrArg₂ (CollarWeakDerivative lower)
      (collarScalar_inverse_apply lower a b inverse v)
      (collarScalar_inverse_slope lower a ad b bd inverse cancel v d)).mp result
  · exact collarWeakDerivative_scalar lower a ad da v d

def annularForwardPhase (parameters : PhaseParameters) (cell : ℤ) : C(ℝ, ℝ) :=
  ⟨fun radius => Real.exp (radialPhase parameters radius cell),
    Real.continuous_exp.comp (radialPhase_smooth parameters cell).continuous⟩
def annularForwardPhaseSlope (parameters : PhaseParameters) (cell : ℤ) : C(ℝ, ℝ) :=
  ⟨fun radius => annularPhaseSlope parameters cell radius * annularForwardPhase parameters cell radius,
    (annularPhaseSlope_continuous parameters cell).mul (annularForwardPhase parameters cell).continuous⟩

theorem annularForwardPhase_hasDerivAt (parameters : PhaseParameters) (cell : ℤ) (radius : ℝ) :
    HasDerivAt (annularForwardPhase parameters cell) (annularForwardPhaseSlope parameters cell radius) radius := by
  change HasDerivAt (fun point => Real.exp (radialPhase parameters point cell))
    (annularPhaseSlope parameters cell radius * Real.exp (radialPhase parameters radius cell)) radius
  rw [mul_comm]
  exact (radialPhase_hasDerivAt parameters cell radius).exp

theorem annularPhase_weak_iff (parameters : PhaseParameters) (lower : ℝ) (cell : ℤ)
    (v d : CollarL2 (ComplexEuclidean 1) lower) :
    CollarWeakDerivative lower (collarScalar 1 lower (annularInversePhase parameters cell) v)
      (collarScalar 1 lower (annularInversePhaseSlope parameters cell) v +
        collarScalar 1 lower (annularInversePhase parameters cell) d) ↔ CollarWeakDerivative lower v d :=
  collarWeakDerivative_conjugation lower (annularInversePhase parameters cell) (annularInversePhaseSlope parameters cell)
    (annularForwardPhase parameters cell) (annularForwardPhaseSlope parameters cell)
    (annularInversePhase_hasDerivAt parameters cell) (annularForwardPhase_hasDerivAt parameters cell)
    (fun radius => by
      change Real.exp (radialPhase parameters radius cell) * Real.exp (-radialPhase parameters radius cell) = 1
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero])
    (fun radius => by
      change (annularPhaseSlope parameters cell radius * annularForwardPhase parameters cell radius) *
        annularInversePhase parameters cell radius + annularForwardPhase parameters cell radius *
          (-annularPhaseSlope parameters cell radius * annularInversePhase parameters cell radius) = 0
      ring) v d

theorem collarWeakDerivative_smul_iff (lower : ℝ) (c : ℂ) (nonzero : c ≠ 0)
    (v d : CollarL2 (ComplexEuclidean 1) lower) :
    CollarWeakDerivative lower (c • v) (c • d) ↔ CollarWeakDerivative lower v d := by
  constructor
  · intro weak
    have result := collarWeakDerivative_complex_smul lower c⁻¹ _ _ weak
    simpa only [inv_smul_smul₀ nonzero] using result
  · exact collarWeakDerivative_complex_smul lower c v d

end Grad.AnnularFourSource
