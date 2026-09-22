import AKBD17SameDeterminantProductExpansion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualDeterminantEquations
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.ActualSmoothPhysicalField Grad.ActualCartesianEquations
open Grad.ActualOriginalThirdSource Grad.ExhaustionSourceAllocation Grad.QuotientProjection Grad.FlatSourceProjection
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollar

open Grad.AnnularReconstruction Grad.GaugeCoefficients.Physical.Ledger Grad.ActualPolarFlux

/-- The signed second polar cofactor row is exactly the original physical
kappa. -/
theorem sameCofactorEntry_kappa (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact) (radius : RadialPoint) (angles : ℝ × ℝ) (component : Fin 3) :
    originalCofactorSmoothEntry parameters length compact state 1 component radius.val angles =
      physicalKappa angles.1 (originalPhysicalSignedCofactor parameters length state.val.val.epsilon state.val.val.field angles.2
        (polarClosedPoint radius.val angles.1 radius.property.1 radius.property.2)) component := by
  rw [originalCofactorSmoothEntry_literal]
  fin_cases component <;> rfl

/-- Literal G3 correction in the SAME primitive-source coordinates. In
particular the signed kappa_2 includes the circular -F0/r term. -/
theorem physicalCorrection_sameCofactor (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact) (source : SmoothQuotient parameters)
    (radius : RadialPoint) (angles : ℝ × ℝ) :
    physicalCorrection parameters length state.val.val.epsilon state.val.val.field source radius.val radius.property.1 radius.property.2 angles 0 =
      (originalCofactorSmoothEntry parameters length compact state 1 0 radius.val angles *
          literalPrimitiveSource parameters length source radius.val radius.property.1 radius.property.2 0 angles 0 +
        originalCofactorSmoothEntry parameters length compact state 1 1 radius.val angles *
          literalPrimitiveSource parameters length source radius.val radius.property.1 radius.property.2 1 angles 0 -
        originalCofactorSmoothEntry parameters length compact state 1 2 radius.val angles *
          literalPrimitiveSource parameters length source radius.val radius.property.1 radius.property.2 2 angles 0) / (radius.val : ℂ) := by
  rw [sameCofactorEntry_kappa parameters length compact state radius angles 0,
    sameCofactorEntry_kappa parameters length compact state radius angles 1,
    sameCofactorEntry_kappa parameters length compact state radius angles 2]
  simp [physicalCorrection,physicalKappaDeviation,physicalDividedSources,literalPrimitiveSource,
    radialProjection_component,tangentialProjection_component,Grad.Constraints.polarRadialComponent,
    Grad.Constraints.polarTangentialComponent,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,
    smul_eq_mul,Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv]
  ring

/-- The actual scalar g has zero circular mean, with all integer cells retained. -/
theorem literalScalarSource_meanFree (parameters : PhaseParameters) (source : SmoothQuotient parameters)
    (flat : IsFlat source) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    removePolarMean (corePolarValue parameters (source 2) radius nonnegative bounded) =
      corePolarValue parameters (source 2) radius nonnegative bounded := by
  apply meanFree_of_doubleCoefficient_zero _ (corePolarValue_continuous parameters (source 2) radius nonnegative bounded)
    (fun axial polar => corePolarValue_polar_shift parameters (source 2) radius nonnegative bounded polar axial)
    (fun polar axial => corePolarValue_axial_shift parameters (source 2) radius nonnegative bounded polar axial)
  intro cell
  change angularCoefficient (fun polar => angularCoefficient (fun axial => corePolarValue parameters (source 2) radius nonnegative bounded (polar,axial)) cell) 0 = 0
  simp_rw [corePolarValue_axialCoefficient]
  exact originalScalarCircle_mean_zero parameters (source 2) ((isFlat_iff_cartesian source).mp flat).2.2.2.1 cell radius nonnegative bounded

end Grad.ActualDeterminantEquations
