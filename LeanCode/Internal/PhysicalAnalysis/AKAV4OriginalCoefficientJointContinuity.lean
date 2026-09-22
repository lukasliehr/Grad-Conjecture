import AKAV3SameLiteralG3PhysicalField

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualOriginalThirdSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.SourceCollarFullSource Grad.SourceCollarBulk Grad.SourceCollarRestriction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarFlux Grad.BoundaryTrace Grad.SourceCollar
open Grad.AnnularGeneralSourceRegularity Grad.AnnularCurrentLow Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularStrongOrbit Grad.AnnularSourceGraph Grad.AnnularForwardDatum Grad.AnnularRestriction
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.Allocation Grad.BoundaryLift

open Grad.AnnularKernelL2 Grad.ActualCurrentPrimitives Grad.AnnularReconstruction Grad.AnnularKernelContinuity

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)

private def kappaContinuousMajorant (mode : ℤ × ℤ) : ℝ :=
  (kappaFourierConstant parameters length 4 0 * physicalBudget parameters field rho epsilon 9) *
    (annularFrequency mode.1 mode.2 ^ 4)⁻¹

include small in
private theorem kappaContinuousMajorant_bound (component : Fin 3) (r : RadialPoint) (mode : ℤ × ℤ) :
    ‖kappaScalar parameters length rho epsilon field small component 0 r.val mode‖ ≤
      kappaContinuousMajorant parameters length rho epsilon field mode := by
  unfold kappaContinuousMajorant
  rw [← div_eq_mul_inv,le_div_iff₀ (pow_pos (annularFrequency_pos mode) 4)]
  have term := (kappaScalarMoment_summable parameters length rho epsilon field small component 4 0 r.val r.property.1 r.property.2).le_tsum mode
    (fun other _ => productMoment_nonnegative parameters 4 r.val _ other)
  have estimate := term.trans (kappaScalarMoment_bound parameters length rho epsilon field small component 4 0 r.val r.property.1 r.property.2)
  apply le_trans _ estimate
  have weighted := mul_le_mul_of_nonneg_right (coefficientRadialEnvelope_one_le parameters r.val r.property.1 r.property.2 mode.2)
    (mul_nonneg (pow_nonneg (annularFrequency_pos mode).le 4)
      (norm_nonneg (kappaScalar parameters length rho epsilon field small component 0 r.val mode)))
  change ‖kappaScalar parameters length rho epsilon field small component 0 r.val mode‖ * annularFrequency mode.1 mode.2 ^ 4 ≤
    coefficientRadialEnvelope parameters mode.2 r.val * annularFrequency mode.1 mode.2 ^ 4 *
      ‖kappaScalar parameters length rho epsilon field small component 0 r.val mode‖
  nlinarith only [weighted]

include small in
/-- Joint continuity uses the existing full-cell synthesis and its already proved original moments. -/
theorem physicalKappaDeviation_joint_continuous (component : Fin 3) :
    Continuous (fun query : RadialPoint × (ℝ × ℝ) =>
      physicalKappaDeviation parameters length epsilon field query.1.val query.1.property.1 query.1.property.2 component query.2) := by
  simp_rw [physicalKappaDeviation_eq_tsum parameters length rho epsilon field small]
  apply continuous_tsum
    (fun mode : ℤ × ℤ => ((cellExponential_smooth mode.2).continuous.comp (continuous_snd.comp continuous_snd)).mul
      (((cellExponential_smooth mode.1).continuous.comp (continuous_fst.comp continuous_snd)).mul
        ((kappaScalar_continuous parameters length rho epsilon field small component 0 mode).comp
          (continuous_subtype_val.comp continuous_fst))))
    (show Summable (kappaContinuousMajorant parameters length rho epsilon field) from fullLattice_decay_summable.mul_left _) ?_
  intro mode query
  simpa only [Function.comp_apply,Pi.mul_apply,norm_mul,cellExponential_norm,one_mul] using
    kappaContinuousMajorant_bound parameters length rho epsilon field small component query.1 mode

/-- The genuine original closed-jet evaluator gives joint radius/angle continuity of the prescribed Cartesian source. -/
theorem corePolarValue_joint_continuous {dimension : ℕ} (source : ACore parameters dimension) :
    Continuous (fun query : RadialPoint × (ℝ × ℝ) =>
      corePolarValue parameters source query.1.val query.1.property.1 query.1.property.2 query.2) := by
  have pointContinuous : Continuous (fun query : RadialPoint × (ℝ × ℝ) =>
      polarClosedPoint query.1.val query.2.1 query.1.property.1 query.1.property.2) :=
    (polarPlane_smooth.continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_fst.comp continuous_snd))).subtype_mk _
  simp_rw [corePolarValue,sourceCoreValue_eq_originalPhysicalEvaluationLift]
  change Continuous (fun query : RadialPoint × (ℝ × ℝ) => (originalPhysicalClosedJet parameters source).value
    (polarClosedPoint query.1.val query.2.1 query.1.property.1 query.1.property.2,(query.2.2 : CellCircle)))
  exact (originalPhysicalClosedJet parameters source).value.continuous.comp
    (pointContinuous.prodMk ((AddCircle.continuous_mk' _).comp (continuous_snd.comp continuous_snd)))

end Grad.ActualOriginalThirdSource
