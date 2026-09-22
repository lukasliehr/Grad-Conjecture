import AKAT20SamePrimitiveSourceCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualCartesianEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.SourceCollarFullSource Grad.SourceCollarBulk Grad.SourceCollarRestriction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarFlux Grad.BoundaryTrace Grad.SourceCollar
open Grad.AnnularGeneralSourceRegularity Grad.AnnularCurrentLow Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularStrongOrbit Grad.AnnularSourceGraph Grad.AnnularForwardDatum Grad.AnnularRestriction
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.Allocation Grad.BoundaryLift Grad.ActualOriginalThirdSource
open Grad.AnnularSmoothCore Grad.AnnularKernelL2 Grad.AnnularReconstruction

theorem literalPrimitiveSource_periodic (parameters : PhaseParameters) (length : ℝ) (source : SmoothQuotient parameters)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (component : Fin 3) :
    (∀ axial,Function.Periodic (fun polar => literalPrimitiveSource parameters length source radius nonnegative bounded component (polar,axial)) (2*Real.pi)) ∧
    (∀ polar,Function.Periodic (fun axial => literalPrimitiveSource parameters length source radius nonnegative bounded component (polar,axial)) (2*Real.pi)) := by
  constructor
  · intro axial polar
    fin_cases component <;> simp [literalPrimitiveSource,radialProjection,tangentialProjection,corePolarValue_polar_shift,
      Real.cos_add_two_pi,Real.sin_add_two_pi]
  · intro polar axial
    fin_cases component <;> simp [literalPrimitiveSource,corePolarValue_axial_shift]

def clampedLiteralPrimitiveSource (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (source : SmoothQuotient parameters)
    (component : Fin 3) (query : ℝ × (ℝ × ℝ)) : ComplexEuclidean 1 :=
  let r := collarRadius lower positive bounded.le query.1
  literalPrimitiveSource parameters length source r.val r.property.1 r.property.2 component query.2

theorem clampedLiteralPrimitiveSource_continuous (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (source : SmoothQuotient parameters) (component : Fin 3) :
    Continuous (clampedLiteralPrimitiveSource parameters length lower positive bounded source component) := by
  fin_cases component
  · exact (radialProjection_continuous.comp (continuous_fst.comp continuous_snd)).clm_apply
      (clampedCorePolarValue_continuous parameters lower positive bounded (cartesianSourceVector source))
  · exact (tangentialProjection_continuous.comp (continuous_fst.comp continuous_snd)).clm_apply
      (clampedCorePolarValue_continuous parameters lower positive bounded (cartesianSourceVector source))
  · exact (clampedCorePolarValue_continuous parameters lower positive bounded (source 3)).const_smul ((length : ℂ)⁻¹)

theorem clampedLiteralPrimitiveSource_eq (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (source : SmoothQuotient parameters) (component : Fin 3)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    clampedLiteralPrimitiveSource parameters length lower positive bounded source component (radius,angles) =
      literalPrimitiveSource parameters length source radius (positive.le.trans inside.1) inside.2 component angles := by
  have point : collarRadius lower positive bounded.le radius =
      (⟨radius,positive.le.trans inside.1,inside.2⟩ : RadialPoint) :=
    Subtype.ext (collarRadius_literal lower positive bounded.le radius inside)
  simp only [clampedLiteralPrimitiveSource,point]

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (data : OriginalStrongCarrier parameters lower 0 0)
    (same : data.val.ofLp.1 =
      (actualOriginalSourceDatum parameters length rho epsilon field small lower positive bounded 0 source flat).val.ofLp.1)
    (component : Fin 3)
    (curves : SmoothLowPhysicalRow parameters lower positive
      (strongKnownBulk parameters lower positive bounded.le
        (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data) (primitiveKnownSlot component)))
include same

theorem sameKnownSource_fullField_literal_ae :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ angles : ℝ × ℝ,
      curves.fullField bounded (radius,angles) =
        literalPrimitiveSource parameters length source radius (positive.le.trans inside.1) inside.2 component angles := by
  filter_upwards [sameKnownSource_physicalCoefficients parameters length rho epsilon field small
      lower positive bounded lengthPositive source flat data same component,
    curves.physicalCurve_actual bounded 0] with radius original represented
  intro inside angles
  have periodic := literalPrimitiveSource_periodic parameters length source radius (positive.le.trans inside.1) inside.2 component
  apply congrFun (curves.fullField_eq_of_doubleCoefficient bounded radius inside
    (literalPrimitiveSource parameters length source radius (positive.le.trans inside.1) inside.2 component)
    (literalPrimitiveSource_continuous parameters length source radius (positive.le.trans inside.1) inside.2 component)
    periodic.1 periodic.2 ?_) angles
  intro mode
  exact (original inside mode).symm.trans (by simpa only [pow_zero,one_smul] using (represented mode).symm)

/-- SAME actual F1,F0,F2 at every closed-collar radius and both original angles. -/
theorem sameKnownSource_fullField_literal
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    curves.fullField bounded (radius,angles) =
      literalPrimitiveSource parameters length source radius (positive.le.trans inside.1) inside.2 component angles := by
  have agreement := collarCurve_eq_of_ae lower bounded
    (fun current => curves.fullField bounded (current,angles))
    (fun current => clampedLiteralPrimitiveSource parameters length lower positive bounded source component (current,angles))
    ((curves.fullField_smooth bounded).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun current member => ⟨member,mem_univ _⟩))
    (((clampedLiteralPrimitiveSource_continuous parameters length lower positive bounded source component).comp
      (continuous_id.prodMk continuous_const)).continuousOn) ?_
  · exact (agreement inside).trans (clampedLiteralPrimitiveSource_eq parameters length lower positive bounded source component radius inside angles)
  · filter_upwards [sameKnownSource_fullField_literal_ae parameters length rho epsilon field small
      lower positive bounded lengthPositive source flat data same component curves,ae_restrict_mem measurableSet_Icc] with current actual member
    exact (actual member angles).trans
      (clampedLiteralPrimitiveSource_eq parameters length lower positive bounded source component current member angles).symm

end Grad.ActualCartesianEquations
