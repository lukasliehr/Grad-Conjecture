import AKAT18OriginalCartesianSourceDecode

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualCartesianEquations
open Grad.AnnularCurrentSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.SourceCollarFullSource Grad.SourceCollarBulk Grad.SourceCollarRestriction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarFlux Grad.BoundaryTrace Grad.SourceCollar
open Grad.AnnularGeneralSourceRegularity Grad.AnnularCurrentLow Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularStrongOrbit Grad.AnnularSourceGraph Grad.AnnularForwardDatum Grad.AnnularRestriction
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.Allocation Grad.BoundaryLift Grad.ActualOriginalThirdSource Grad.BoundaryKernelAction

/-- Original primitive F1,F0,F2, before the division occurring only in G3. -/
def literalPrimitiveSource (parameters : PhaseParameters) (length : ℝ) (source : SmoothQuotient parameters)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (component : Fin 3)
    (angles : ℝ × ℝ) : ComplexEuclidean 1 :=
  ![radialProjection angles.1 (corePolarValue parameters (cartesianSourceVector source) radius nonnegative bounded angles),
    tangentialProjection angles.1 (corePolarValue parameters (cartesianSourceVector source) radius nonnegative bounded angles),
    (length : ℂ)⁻¹ • corePolarValue parameters (source 3) radius nonnegative bounded angles] component

def primitiveKnownSlot : Fin 3 → Fin 4 := ![3,0,2]

theorem literalPrimitiveSource_continuous (parameters : PhaseParameters) (length : ℝ) (source : SmoothQuotient parameters)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (component : Fin 3) :
    Continuous (literalPrimitiveSource parameters length source radius nonnegative bounded component) := by
  fin_cases component
  · exact (radialProjection_continuous.comp continuous_fst).clm_apply (corePolarValue_continuous parameters _ radius nonnegative bounded)
  · exact (tangentialProjection_continuous.comp continuous_fst).clm_apply (corePolarValue_continuous parameters _ radius nonnegative bounded)
  · exact (corePolarValue_continuous parameters _ radius nonnegative bounded).const_smul ((length : ℂ)⁻¹)

theorem literalPrimitiveSource_doubleCoefficient (parameters : PhaseParameters) (length : ℝ) (source : SmoothQuotient parameters)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (component : Fin 3) (mode : ℤ × ℤ) :
    doubleCoefficient (literalPrimitiveSource parameters length source radius nonnegative bounded component) mode =
      angularCoefficient (fun angle =>
        ![radialPolarField (fun theta => ((cartesianSourceVector source).val mode.2).value (polarClosedPoint radius theta nonnegative bounded)) angle,
          tangentialPolarField (fun theta => ((cartesianSourceVector source).val mode.2).value (polarClosedPoint radius theta nonnegative bounded)) angle,
          (length : ℂ)⁻¹ • ((source 3).val mode.2).value (polarClosedPoint radius angle nonnegative bounded)] component) mode.1 := by
  have sectionContinuous (polar : ℝ) : Continuous (fun axial => corePolarValue parameters (cartesianSourceVector source) radius nonnegative bounded (polar,axial)) := (corePolarValue_continuous parameters (cartesianSourceVector source) radius nonnegative bounded).comp
    (continuous_const.prodMk continuous_id (X := ℝ))
  fin_cases component
  · change angularCoefficient (fun polar => angularCoefficient (fun axial => radialProjection polar
      (corePolarValue parameters (cartesianSourceVector source) radius nonnegative bounded (polar,axial))) mode.2) mode.1 = _
    simp_rw [angularCoefficient_valueMap _ _ (sectionContinuous _),corePolarValue_axialCoefficient]
    apply congrArg (fun field => angularCoefficient field mode.1)
    funext angle
    exact radialProjection_apply angle (fun theta => ((cartesianSourceVector source).val mode.2).value (polarClosedPoint radius theta nonnegative bounded))
  · change angularCoefficient (fun polar => angularCoefficient (fun axial => tangentialProjection polar
      (corePolarValue parameters (cartesianSourceVector source) radius nonnegative bounded (polar,axial))) mode.2) mode.1 = _
    simp_rw [angularCoefficient_valueMap _ _ (sectionContinuous _),corePolarValue_axialCoefficient]
    apply congrArg (fun field => angularCoefficient field mode.1)
    funext angle
    exact tangentialProjection_apply angle (fun theta => ((cartesianSourceVector source).val mode.2).value (polarClosedPoint radius theta nonnegative bounded))
  · change angularCoefficient (fun polar => angularCoefficient ((length : ℂ)⁻¹ •
      (fun axial => corePolarValue parameters (source 3) radius nonnegative bounded (polar,axial))) mode.2) mode.1 = _
    simp_rw [angularCoefficient_smul_continuous,corePolarValue_axialCoefficient]
    rfl

/-- All three exact original primitive source rows decode to the unchanged
Cartesian source. The auxiliary RF0 slot is not substituted for F0. -/
theorem actualPrimitiveSources_originalCoefficients (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (source : SmoothQuotient parameters) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ (component : Fin 3) (mode : ℤ × ℤ),
      originalRowCoefficient parameters 0 lower
        (actualCartesianPrimitiveRows parameters length lower positive bounded source (primitiveKnownSlot component)) radius mode =
      doubleCoefficient (literalPrimitiveSource parameters length source radius (positive.le.trans inside.1) inside.2 component) mode := by
  let planar := cartesianWeightedRadialRow parameters lower positive bounded (cartesianSourceVector source) 0 0
  filter_upwards [originalCartesianRow_physicalCoefficients parameters lower positive bounded (cartesianSourceVector source),
    originalCartesianRow_physicalCoefficients parameters lower positive bounded (source 3),
    radialRowContraction_decoded_ae parameters lower positive planar,
    tangentialRowContraction_decoded_ae parameters lower positive planar,
    originalRowCoefficient_smul_ae parameters 0 lower (length : ℂ)⁻¹
      (cartesianWeightedRadialRow parameters lower positive bounded (source 3) 0 0)] with radius planarSame scalarSame radial tangential scaled
  intro inside component mode
  have continuousPlanar : Continuous (fun angle => ((cartesianSourceVector source).val mode.2).value
      (polarClosedPoint radius angle (positive.le.trans inside.1) inside.2)) :=
    ((cartesianSourceVector source).val mode.2).value.continuous.comp
      ((polarPlane_smooth.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _)
  rw [literalPrimitiveSource_doubleCoefficient]
  fin_cases component
  · change originalRowCoefficient parameters 0 lower (actualOriginalF1Row parameters lower positive bounded.le 0 source) radius mode = angularCoefficient (radialPolarField (fun angle => ((cartesianSourceVector source).val mode.2).value (polarClosedPoint radius angle (positive.le.trans inside.1) inside.2))) mode.1
    rw [actualOriginalF1Bulk_exact parameters lower positive bounded source,radial mode,
      radialPolarField_coefficient _ continuousPlanar]
    simp only [planar,planarSame inside]
  · change originalRowCoefficient parameters 0 lower (unweightedSourceF0Bulk parameters lower (actualOriginalF0Graph parameters lower positive bounded 0 source)) radius mode = angularCoefficient (tangentialPolarField (fun angle => ((cartesianSourceVector source).val mode.2).value (polarClosedPoint radius angle (positive.le.trans inside.1) inside.2))) mode.1
    rw [actualOriginalF0Bulk_exact parameters lower positive bounded source,tangential mode,
      tangentialPolarField_coefficient _ continuousPlanar]
    simp only [planar,planarSame inside]
  · change originalRowCoefficient parameters 0 lower (unweightedSourceF2Bulk parameters lower (actualOriginalF2Graph parameters length lower positive bounded 0 source)) radius mode = angularCoefficient ((length : ℂ)⁻¹ • (fun angle => ((source 3).val mode.2).value (polarClosedPoint radius angle (positive.le.trans inside.1) inside.2))) mode.1
    rw [actualOriginalF2Bulk_exact parameters lower positive bounded source length,scaled mode,
      scalarSame inside mode]
    exact (angularCoefficient_smul_continuous (length : ℂ)⁻¹ _ mode.1).symm

end Grad.ActualCartesianEquations
