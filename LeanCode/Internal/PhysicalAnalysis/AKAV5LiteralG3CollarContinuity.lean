import AKAV4OriginalCoefficientJointContinuity

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

open Grad.AnnularKernelL2 Grad.AnnularReconstruction

private theorem angularCoefficient_joint_parameter_continuous {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (field : (ℝ × (ℝ × ℝ)) × ℝ → Value) (continuousField : Continuous field) (mode : ℤ) :
    Continuous (fun parameter => angularCoefficient (fun angle => field (parameter,angle)) mode) := by
  simp_rw [angularCoefficient_compact_general]
  exact (continuous_const : Continuous (fun _ : ℝ × (ℝ × ℝ) => (2*Real.pi)⁻¹)).smul
    (continuous_parametric_integral_of_continuous
      (((cellExponential_smooth (-mode)).continuous.comp continuous_snd).smul continuousField) isCompact_Icc)

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (source : SmoothQuotient parameters)

def clampedPhysicalG3 (query : ℝ × (ℝ × ℝ)) : ComplexEuclidean 1 :=
  let r := collarRadius lower positive bounded.le query.1
  physicalG3 parameters length epsilon field source r.val r.property.1 r.property.2 query.2

theorem clampedCorePolarValue_continuous {dimension : ℕ} (core : ACore parameters dimension) :
    Continuous (fun query : ℝ × (ℝ × ℝ) =>
      let r := collarRadius lower positive bounded.le query.1
      corePolarValue parameters core r.val r.property.1 r.property.2 query.2) :=
  (corePolarValue_joint_continuous parameters core).comp
    (((collarRadius_continuous lower positive bounded.le).comp continuous_fst).prodMk continuous_snd)

theorem clampedDividedSource_continuous (component : Fin 3) :
    Continuous (fun query : ℝ × (ℝ × ℝ) =>
      let r := collarRadius lower positive bounded.le query.1
      physicalDividedSources parameters length source r.val r.property.1 r.property.2 component query.2) := by
  have reciprocal : Continuous (fun query : ℝ × (ℝ × ℝ) =>
      (collarRadius lower positive bounded.le query.1).val⁻¹) :=
    ((continuous_subtype_val.comp (collarRadius_continuous lower positive bounded.le)).comp continuous_fst).inv₀
      (fun query => (positive.trans_le (collarRadius_lower lower positive bounded.le query.1)).ne')
  have planar := reciprocal.smul (clampedCorePolarValue_continuous parameters lower positive bounded (cartesianSourceVector source))
  have fourth := reciprocal.smul (clampedCorePolarValue_continuous parameters lower positive bounded (source 3))
  fin_cases component
  · exact (radialProjection_continuous.comp (continuous_fst.comp continuous_snd)).clm_apply planar
  · exact (tangentialProjection_continuous.comp (continuous_fst.comp continuous_snd)).clm_apply planar
  · exact (continuous_const : Continuous (fun _ : ℝ × (ℝ × ℝ) => (length : ℂ)⁻¹)).smul fourth

include small in
theorem clampedCorrection_continuous :
    Continuous (fun query : ℝ × (ℝ × ℝ) =>
      let r := collarRadius lower positive bounded.le query.1
      physicalCorrection parameters length epsilon field source r.val r.property.1 r.property.2 query.2) := by
  have kappa (component : Fin 3) := (physicalKappaDeviation_joint_continuous parameters length rho epsilon field small component).comp
    (((collarRadius_continuous lower positive bounded.le).comp continuous_fst).prodMk continuous_snd)
  have divided := clampedDividedSource_continuous parameters length lower positive bounded source
  exact ((((kappa 0).smul (divided 0)).add ((kappa 1).smul (divided 1))).sub
    ((kappa 2).smul (divided 2))).sub (divided 1)

include small in
/-- The literal full G3 has a continuous extension along the SAME positive collar, including its endpoints. -/
theorem clampedPhysicalG3_continuous :
    Continuous (clampedPhysicalG3 parameters length epsilon field lower positive bounded source) := by
  let correctionField := fun query : ℝ × (ℝ × ℝ) =>
    let r := collarRadius lower positive bounded.le query.1
    physicalCorrection parameters length epsilon field source r.val r.property.1 r.property.2 query.2
  have correction : Continuous correctionField :=
    clampedCorrection_continuous parameters length rho epsilon field small lower positive bounded source
  let lift : (ℝ × (ℝ × ℝ)) × ℝ → ℝ × (ℝ × ℝ) := fun input => (input.1.1,input.2,input.1.2.2)
  have liftContinuous : Continuous lift := by fun_prop
  have average := angularCoefficient_joint_parameter_continuous (correctionField ∘ lift) (correction.comp liftContinuous) 0
  change Continuous (fun query : ℝ × (ℝ × ℝ) =>
    (length : ℂ)⁻¹ • corePolarValue parameters (source 2)
      (collarRadius lower positive bounded.le query.1).val
      (collarRadius lower positive bounded.le query.1).property.1 (collarRadius lower positive bounded.le query.1).property.2 query.2 +
      (correctionField query - angularCoefficient (fun polar => (correctionField ∘ lift) (query,polar)) 0))
  exact ((continuous_const : Continuous (fun _ : ℝ × (ℝ × ℝ) => (length : ℂ)⁻¹)).smul
    (clampedCorePolarValue_continuous parameters lower positive bounded (source 2))).add (correction.sub average)

theorem clampedPhysicalG3_literal (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    clampedPhysicalG3 parameters length epsilon field lower positive bounded source (radius,angles) =
      physicalG3 parameters length epsilon field source radius (positive.le.trans inside.1) inside.2 angles := by
  have point : collarRadius lower positive bounded.le radius =
      (⟨radius,positive.le.trans inside.1,inside.2⟩ : RadialPoint) :=
    Subtype.ext (collarRadius_literal lower positive bounded.le radius inside)
  simp only [clampedPhysicalG3,point]

end Grad.ActualOriginalThirdSource
