import AID4LiteralSingleFluxPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularCurrentGreen
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularCircularForm
open Grad.AnnularTiltedReference Grad.AnnularGrades Grad.CircularHighRegularity Grad.AnnularSourceGraph

variable (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))

/-- The actual compact physical packet equation, with genuine smooth radial tests. -/
def CompactPhysicalPacketEquation (field : DivisionRow 3 lower) : Prop :=
  ∀ (mode : HighAnnularMode) (profile : ℝ → ℝ) (smooth : ContDiff ℝ ∞ profile),
    HasCompactSupport profile → tsupport profile ⊆ Ioo lower 1 → ∀ vector : ComplexEuclidean 1,
    inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength
      (bEnergyNormalize lower L positive (annularScalarTest lower L positive mode profile smooth vector))) field = 0

/-- Compact physical testing gives the weak derivative of r times the SAME recovered X. -/
theorem physicalFluxMoment_compactWeak (field : DivisionRow 3 lower)
    (equation : CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength field)
    (mode : HighAnnularMode) :
    CompactWeakDerivative 1 lower
      (annularRadialMoment lower positive (highPhysicalOutput lower 0 field mode))
      (physicalFluxMomentRHS parameters lower L positive field mode) := by
  intro profile smooth compact supported vector
  have law := equation mode profile smooth compact supported vector
  rw [physicalTestPacket_scalar_moment] at law
  change collarPairing lower ⟨profile, smooth.continuous⟩ vector (physicalFluxMomentRHS parameters lower L positive field mode) =
    -collarPairing lower ⟨deriv profile, (contDiff_infty_iff_deriv.mp smooth).2.continuous⟩ vector
      (annularRadialMoment lower positive (highPhysicalOutput lower 0 field mode))
  linear_combination law

/-- Concrete ordinary radial derivative of the SAME normalized physical X. -/
def physicalFluxOrdinarySlope (field : DivisionRow 3 lower) (mode : HighAnnularMode) :
    CollarL2 (ComplexEuclidean 1) lower :=
  collarScalar 1 lower (annularInverseRadiusSlope lower positive)
      (annularRadialMoment lower positive (highPhysicalOutput lower 0 field mode)) +
    collarScalar 1 lower (annularInverseRadiusCurve lower positive)
      (physicalFluxMomentRHS parameters lower L positive field mode)

/-- No independent derivative or endpoint datum is introduced: compact tests force the actual weak radial graph. -/
theorem physicalFluxOrdinary_weak (bounded : lower < 1) (field : DivisionRow 3 lower)
    (equation : CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength field)
    (mode : HighAnnularMode) :
    CollarWeakDerivative lower (radialOrdinary 1 lower positive (highPhysicalOutput lower 0 field mode))
      (physicalFluxOrdinarySlope parameters lower L positive field mode) := by
  have moment := physicalFluxMoment_compactWeak parameters lower L positive lengthPositive widthHalf widthLength field equation mode
  have divided := compactWeakDerivative_divide_radius lower positive _ _ moment
  rw [annularRadialMoment_divide] at divided
  exact (compactWeak_iff_collarWeak 1 lower positive bounded _ _).mp divided

end Grad.AnnularCurrentGreen
