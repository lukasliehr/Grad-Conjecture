import AJN1ActualHighStorageRemoval

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.AnnularHighRadial
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.CircularHighWeak
open Grad.AnnularVariational Grad.AnnularReconstruction Grad.AnnularHighTilt Grad.AnnularTiltedReference
open Grad.AnnularRegularity Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.AnnularCurrentEnergy
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)

def rawHighXiSection (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    RadialContinuousSection 1 lower :=
  radialSectionScalar lower (rawHighPhase parameters lower positive mode.val.2)
    (weightedRadialSection 1 lower positive bounded
      (annularModeRadialH1 lower length positive mode (bEnergyDecode lower length positive field)))

theorem rawHighXiSection_same (field : annularEnergySpace lower length positive) (mode : HighAnnularMode)
    (radius : Icc lower (1 : ℝ)) :
    rawHighXiSection parameters lower length positive bounded field mode radius =
      highPowerCurve lower highTiltExponent positive radius.val •
        annularPhysicalValueSection parameters lower length positive bounded mode
          (bEnergyDecode lower length positive field) radius := by
  exact mul_smul (highPowerCurve lower highTiltExponent positive radius.val)
    (annularInversePhase parameters mode.val.2 radius.val)
    (weightedRadialSection 1 lower positive bounded
      (annularModeRadialH1 lower length positive mode (bEnergyDecode lower length positive field)) radius)

theorem rawHighXiSection_bulk (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    radialSectionL2 1 lower positive bounded.le (rawHighXiSection parameters lower length positive bounded field mode) =
      collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
        (radialOrdinary 1 lower positive (annularEnergyValue lower length positive (bEnergyDecode lower length positive field) mode)) := by
  unfold rawHighXiSection
  rw [radialSectionL2_scalar, weightedRadialSection_bulk, annularEnergyValue_ordinary lower length positive bounded.le]
  rfl

variable (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
  (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem rawHighXi_weak (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    CollarWeakDerivative lower
      (radialSectionL2 1 lower positive bounded.le (rawHighXiSection parameters lower length positive bounded field mode))
      (collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
        (radialOrdinary 1 lower positive (highPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field mode))) := by
  rw [rawHighXiSection_bulk]
  apply rawHighPhase_weak
  have genuine : CollarWeakDerivative lower
      (radialOrdinary 1 lower positive (annularEnergyValue lower length positive (bEnergyDecode lower length positive field) mode))
      (radialOrdinary 1 lower positive (annularEnergyDerivative lower length positive (bEnergyDecode lower length positive field) mode)) := by
    rw [annularEnergyValue_ordinary lower length positive bounded.le,
      annularEnergyDerivative_ordinary lower length positive bounded.le]
    exact annularModeRadialH1_weak lower length positive bounded.le mode (bEnergyDecode lower length positive field)
  have same : radialOrdinary 1 lower positive
      (annularEnergyDerivative lower length positive (bEnergyDecode lower length positive field) mode) =
      collarScalar 1 lower (annularTiltCurve parameters lower positive mode.val.2)
        (radialOrdinary 1 lower positive (annularEnergyValue lower length positive (bEnergyDecode lower length positive field) mode)) +
      radialOrdinary 1 lower positive (highPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field mode) := by
    change _ = _ + radialOrdinary 1 lower positive
      (annularEnergyDerivative lower length positive (bEnergyDecode lower length positive field) mode -
        annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength (bEnergyDecode lower length positive field) mode)
    rw [map_sub, annularTiltEnergyPhase_mode, radialOrdinary_collarScalar]
    abel
  rw [← same]
  exact genuine

/-- A continuous candidate identified with the exact actual first row gives
the derivative of this SAME raw Xi section, including both endpoints. -/
theorem rawHighXi_hasDerivWithinAt (field : annularEnergySpace lower length positive) (mode : HighAnnularMode)
    (rhs : C(ℝ, ComplexEuclidean 1))
    (same : collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
      (radialOrdinary 1 lower positive (highPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field mode))
        =ᵐ[volume.restrict (Icc lower 1)] rhs)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (radialSectionExtension 1 lower bounded.le
      (rawHighXiSection parameters lower length positive bounded field mode)) (rhs radius) (Icc lower 1) radius :=
  annularSection_derivative_of_weak lower positive bounded _ _
    (rawHighXi_weak parameters lower length positive bounded lengthPositive widthHalf widthLength field mode)
    _ rfl rhs same radius inside

end Grad.AnnularHighRadial
