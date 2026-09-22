import SC7ActualMeans

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.SourceCollar

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.FlatSourceProjection Grad.NonlinearProduct
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger

/-- Bulk source coordinates and the prescribed physical outer datum are
different pieces of data. -/
structure AnnularSourcePacket where
  bulk : AnnularBulkSource
  physicalOuterDatum : ℝ → ℂ

def attachPhysicalOuterDatum (bulk : AnnularBulkSource)
    (physicalOuterDatum : ℝ → ℂ) : AnnularSourcePacket :=
  ⟨bulk, physicalOuterDatum⟩

@[simp] theorem attachPhysicalOuterDatum_bulk (bulk : AnnularBulkSource)
    (physicalOuterDatum : ℝ → ℂ) :
    (attachPhysicalOuterDatum bulk physicalOuterDatum).bulk = bulk := rfl

@[simp] theorem attachPhysicalOuterDatum_value (bulk : AnnularBulkSource)
    (physicalOuterDatum : ℝ → ℂ) :
    (attachPhysicalOuterDatum bulk physicalOuterDatum).physicalOuterDatum =
      physicalOuterDatum := rfl

def attachHomogeneousPhysicalOuterDatum (bulk : AnnularBulkSource) : AnnularSourcePacket :=
  attachPhysicalOuterDatum bulk 0

@[simp] theorem attachHomogeneousPhysicalOuterDatum_bulk (bulk : AnnularBulkSource) :
    (attachHomogeneousPhysicalOuterDatum bulk).bulk = bulk := rfl

@[simp] theorem attachHomogeneousPhysicalOuterDatum_value (bulk : AnnularBulkSource) :
    (attachHomogeneousPhysicalOuterDatum bulk).physicalOuterDatum = 0 := rfl

/-- Repaired BS28--BS32 bulk-conversion prerequisite on the original physical
disk.  The frame, source, factor `1/r`, and cofactor are evaluated at the same
physical point.  The matrix contractions use the frame's domain-column order
`(y₁,y₂,ζ)`.  The explicit low ball supplies genuine nonsingularity; no
inverse premise is assumed.  BS33's induced outer boundary term remains a
separate later problem. -/
def PhysicalBulkSourceConversionGoal : Prop :=
  (∀ angle : ℝ, physicalKappa angle referenceSignedCofactor = ![0, -1, 0]) ∧
  ∀ (parameters : PhaseParameters) (L epsilon : ℝ) (field : ACore parameters 3)
    (_low : originalGradeNorm 4 field + |epsilon| ≤ originalFrameLowRadius parameters L)
    (radius : ℝ) (_radiusPositive : 0 < radius) (bounded : |radius| ≤ 1)
    (_LPositive : 0 < L) (axialAngle : ℝ) (source : CartesianSourceCore parameters),
    CartesianCoreIsFlat source →
    let kappa := actualPhysicalKappaSlice parameters L epsilon field radius bounded axialAngle
    let sourceSlice := actualCartesianSourceSlice source radius bounded axialAngle
    let bulk := actualAnnularBulkSource parameters L epsilon field radius bounded axialAngle source
    (∀ polarAngle,
      let point := polarClosedPoint radius bounded polarAngle
      let frame := originalPhysicalFrameMatrix parameters L epsilon field axialAngle point
      IsUnit frame.det ∧
      frame * frame⁻¹ = 1 ∧
      frame⁻¹ * frame = 1 ∧
      originalPhysicalSignedCofactor parameters L epsilon field axialAngle point =
        frame.det • (frame⁻¹ * (frame⁻¹).transpose) ∧
      kappa polarAngle = physicalKappa polarAngle
        (originalPhysicalSignedCofactor parameters L epsilon field axialAngle point)) ∧
    annularToCartesian radius L kappa bulk = sourceSlice ∧
    (∀ annular : AnnularBulkSource,
      cartesianToAnnular radius L kappa (annularToCartesian radius L kappa annular) = annular) ∧
    bulk.F0 = (fun angle => polarTangentialComponent angle (sourceSlice.planar angle)) ∧
    sourceAngularAverage bulk.F1 = 0 ∧
    sourceAngularAverage bulk.F2 = 0 ∧
    sourceAngularAverage bulk.G3 = 0 ∧
    (attachHomogeneousPhysicalOuterDatum bulk).bulk = bulk ∧
    (attachHomogeneousPhysicalOuterDatum bulk).physicalOuterDatum = 0 ∧
    (∀ physicalOuterDatum : ℝ → ℂ,
      (attachPhysicalOuterDatum bulk physicalOuterDatum).bulk = bulk ∧
      (attachPhysicalOuterDatum bulk physicalOuterDatum).physicalOuterDatum = physicalOuterDatum)

theorem physicalBulkSourceConversion : PhysicalBulkSourceConversionGoal := by
  refine ⟨physicalKappa_reference, ?_⟩
  intro parameters L epsilon field low radius radiusPositive bounded LPositive axialAngle source flat
  dsimp only
  refine ⟨?_, actualAnnularBulkSource_inverse parameters L epsilon field radius bounded
    LPositive axialAngle source,
    cartesianToAnnular_annularToCartesian radius L LPositive _, ?_, ?_⟩
  · intro polarAngle
    let point := polarClosedPoint radius bounded polarAngle
    exact ⟨originalPhysicalFrameMatrix_isUnit_det_of_low parameters L epsilon field low
        axialAngle point,
      originalPhysicalFrameMatrix_mul_inv_of_low parameters L epsilon field low axialAngle point,
      originalPhysicalFrameMatrix_inv_mul_of_low parameters L epsilon field low axialAngle point,
      rfl, rfl⟩
  · funext angle
    rfl
  · obtain ⟨firstMean, secondMean, thirdMean⟩ :=
      actualAnnularBulkSource_means parameters L epsilon field low radius radiusPositive bounded
        axialAngle source flat
    exact ⟨firstMean, secondMean, thirdMean, rfl, rfl,
      fun physicalOuterDatum => ⟨rfl, rfl⟩⟩

/-- Immediate exact consumer of the repaired same-point global conversion. -/
theorem actualPhysicalBulkSourceConversion_ready : PhysicalBulkSourceConversionGoal :=
  physicalBulkSourceConversion

end Grad.SourceCollar
