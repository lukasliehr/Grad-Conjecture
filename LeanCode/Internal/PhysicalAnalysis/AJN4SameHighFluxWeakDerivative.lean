import AJN3ActualSharedHighFirstRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.AnnularHighRadial
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularVariational Grad.AnnularReconstruction
open Grad.AnnularHighTilt Grad.AnnularTiltedReference Grad.AnnularRegularity Grad.CircularHighRegularity
open Grad.AnnularFluxTrace Grad.AnnularOmegaGraph Grad.AnnularCurrentGreen Grad.AnnularCurrentEnergy Grad.AnnularSmoothCore
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < L)

def rawHighXSection (field : annularOmegaGraph lower L positive lengthPositive) (mode : HighAnnularMode) :
    RadialContinuousSection 1 lower :=
  radialSectionScalar lower (rawHighPhase parameters lower positive mode.val.2)
    (annularFluxSection lower positive bounded (annularOmegaIntoNu lower L positive lengthPositive field) mode)

theorem rawHighXSection_same (field : annularOmegaGraph lower L positive lengthPositive) (mode : HighAnnularMode)
    (radius : Icc lower (1 : ℝ)) :
    rawHighXSection parameters lower L positive bounded lengthPositive field mode radius =
      highPowerCurve lower highTiltExponent positive radius.val •
        actualFluxPhysicalSection lower positive bounded parameters
          (annularOmegaIntoNu lower L positive lengthPositive field) mode radius := by
  exact mul_smul (highPowerCurve lower highTiltExponent positive radius.val)
    (annularInversePhase parameters mode.val.2 radius.val)
    (annularFluxSection lower positive bounded (annularOmegaIntoNu lower L positive lengthPositive field) mode radius)

theorem rawHighXSection_bulk (field : annularOmegaGraph lower L positive lengthPositive) (mode : HighAnnularMode) :
    radialSectionL2 1 lower positive bounded.le (rawHighXSection parameters lower L positive bounded lengthPositive field mode) =
      collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
        (radialOrdinary 1 lower positive (field.val 0 mode)) := by
  unfold rawHighXSection
  rw [radialSectionL2_scalar, annularFluxSection_bulk]
  rfl

/-- Literal second-row forcing after exact storage removal. The third packet
coordinate is the actual rV-rg, so its angular term retains the prescribed Rg. -/
def rawHighXPacketRHS (packet : DivisionRow 3 lower) (mode : HighAnnularMode) : CollarL2 (ComplexEuclidean 1) lower :=
  collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
    (-collarScalar 1 lower (highReciprocalRadius lower positive)
        (radialOrdinary 1 lower positive (highPhysicalOutput lower 0 packet mode)) -
      (Complex.I * (((mode.val.2 : ℝ) / L) : ℝ)) •
        radialOrdinary 1 lower positive (highPhysicalOutput lower 1 packet mode) -
      (Complex.I * (mode.val.1 : ℂ)) • collarScalar 1 lower (highReciprocalRadius lower positive)
        (radialOrdinary 1 lower positive (highPhysicalOutput lower 2 packet mode)))

theorem rawHighXPacket_weak (packet : DivisionRow 3 lower) (mode : HighAnnularMode)
    (weak : CollarWeakDerivative lower
      (radialOrdinary 1 lower positive (highPhysicalOutput lower 0 packet mode))
      (physicalFluxOrdinarySlope parameters lower L positive packet mode)) :
    CollarWeakDerivative lower
      (collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
        (radialOrdinary 1 lower positive (highPhysicalOutput lower 0 packet mode)))
      (rawHighXPacketRHS parameters lower L positive packet mode) := by
  apply rawHighPhase_weak
  have slope : physicalFluxOrdinarySlope parameters lower L positive packet mode =
      collarScalar 1 lower (annularTiltCurve parameters lower positive mode.val.2)
        (radialOrdinary 1 lower positive (highPhysicalOutput lower 0 packet mode)) +
      (-collarScalar 1 lower (highReciprocalRadius lower positive)
          (radialOrdinary 1 lower positive (highPhysicalOutput lower 0 packet mode)) -
        (Complex.I * (((mode.val.2 : ℝ) / L) : ℝ)) •
          radialOrdinary 1 lower positive (highPhysicalOutput lower 1 packet mode) -
        (Complex.I * (mode.val.1 : ℂ)) • collarScalar 1 lower (highReciprocalRadius lower positive)
          (radialOrdinary 1 lower positive (highPhysicalOutput lower 2 packet mode))) := by
    rw [physicalFluxOrdinarySlope_literal]
    abel
  rw [← slope]
  exact weak

theorem rawHighX_hasDerivWithinAt (field : annularOmegaGraph lower L positive lengthPositive)
    (packet : DivisionRow 3 lower) (mode : HighAnnularMode)
    (value : field.val 0 = highPhysicalOutput lower 0 packet)
    (weak : CollarWeakDerivative lower
      (radialOrdinary 1 lower positive (highPhysicalOutput lower 0 packet mode))
      (physicalFluxOrdinarySlope parameters lower L positive packet mode))
    (rhs : C(ℝ, ComplexEuclidean 1))
    (same : rawHighXPacketRHS parameters lower L positive packet mode =ᵐ[volume.restrict (Icc lower 1)] rhs)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (radialSectionExtension 1 lower bounded.le
      (rawHighXSection parameters lower L positive bounded lengthPositive field mode)) (rhs radius) (Icc lower 1) radius := by
  apply annularSection_derivative_of_weak lower positive bounded _ _
    (rawHighXPacket_weak parameters lower L positive packet mode weak) _ _ rhs same radius inside
  rw [rawHighXSection_bulk, value]

end Grad.AnnularHighRadial
