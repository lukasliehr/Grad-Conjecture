import ASG14PhysicalCoefficientCompatibility

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryKernelAction Grad.PhaseAlgebra

theorem radialWeightedEnergy_integrable (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : CollarL2 (ComplexEuclidean dimension) lower) :
    IntervalIntegrable (fun radius => radius * ‖field radius‖ ^ 2) volume lower 1 := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le bounded).2
  apply ((Lp.memLp (radialSqrtMap dimension lower field)).norm.integrable_sq).congr
  filter_upwards [radialSqrtMap_ae dimension lower field, ae_restrict_mem measurableSet_Icc]
    with radius stored inside
  rw [stored, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt (positive.le.trans inside.1)]

/-- AH10 in its exact single-integral form on every completed source. The
phase-conjugated derivative is genuine, by annularConjugatedCoordinate_weak. -/
theorem annularSource_literal_norm_sq (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ)
    (field : AnnularSourceH1 parameters dimension lower angular cell) :
    ‖field‖ ^ 2 = ∑' mode : ℤ × ℤ, splitTangentialWeight angular cell mode ^ 2 *
      (∫ radius in lower..1, radius *
        (‖Real.exp (radialPhase parameters radius mode.2) •
          annularSourceCoefficient parameters dimension lower positive bounded angular cell field mode radius‖ ^ 2 +
         ‖annularConjugatedCoordinate parameters dimension lower positive bounded angular cell field mode 1 radius‖ ^ 2)) := by
  rw [annularSource_completed_norm_sq parameters dimension lower positive bounded]
  apply tsum_congr
  intro mode
  congr 1
  simp only [annularSourceCoefficient_conjugation]
  rw [← intervalIntegral.integral_add
    (radialWeightedEnergy_integrable dimension lower positive bounded
      (annularConjugatedCoordinate parameters dimension lower positive bounded angular cell field mode 0))
    (radialWeightedEnergy_integrable dimension lower positive bounded
      (annularConjugatedCoordinate parameters dimension lower positive bounded angular cell field mode 1))]
  apply intervalIntegral.integral_congr
  intro radius _
  ring

/-- Equality of literal physical source coefficients a.e. determines the
whole completed graph, including its derivative and both endpoint values. -/
theorem annularSourceCoefficient_faithful (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ)
    (first second : AnnularSourceH1 parameters dimension lower angular cell)
    (same : ∀ mode : ℤ × ℤ, ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      annularSourceCoefficient parameters dimension lower positive bounded angular cell first mode radius =
      annularSourceCoefficient parameters dimension lower positive bounded angular cell second mode radius) : first = second := by
  apply annularSource_bulk_injective parameters dimension lower positive bounded angular cell
  apply Subtype.ext
  funext mode
  rw [annularSourceCoordinate_apply, annularSourceCoordinate_apply,
    annularConjugatedCoordinate_storage parameters dimension lower positive bounded angular cell first mode 0,
    annularConjugatedCoordinate_storage parameters dimension lower positive bounded angular cell second mode 0]
  congr 2
  apply Lp.ext
  filter_upwards [same mode] with radius sameValue
  rw [← annularSourceCoefficient_conjugation parameters dimension lower positive bounded angular cell first mode radius,
    ← annularSourceCoefficient_conjugation parameters dimension lower positive bounded angular cell second mode radius,
    sameValue]

end Grad.AnnularSourceGraph
