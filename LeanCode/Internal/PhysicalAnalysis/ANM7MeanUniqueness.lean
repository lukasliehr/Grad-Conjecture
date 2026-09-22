import ANM6BoundaryAndNorm

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualMeanInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Radial Grad.NonlinearRange
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

/-- Genuine equivariance implies Rv=Jv by differentiating its rotation orbit. -/
theorem rotationJet_of_equivariant (field : ClosedJet 2)
    (mean : equivariantAverageJet field = field) :
    rotationJet field = valueMapJet quarterValueMap field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have derivative := closedOrbit_hasDerivAt field point 0
  have orbit : (fun angle => field.value (rotatedPoint angle point)) =
      (fun angle => rotationValueMap angle (field.value point)) := by
    funext angle
    simpa only [mean] using equivariantAverageJet_rotation_value field angle point
  rw [orbit, rotatedPoint_zero] at derivative
  rw [valueMapJet_value]
  exact derivative.unique (rotationValue_hasDerivAt_zero _)

variable {L sigma gamma ell : ℝ}

/-- Raw sector zero of the actual compensated coordinates, before gauges. -/
def IsRawMeanState (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell) : Prop :=
  (∀ cell, angularClosedJet 0 (apSmoothJet admissible 1 cell state.1) =
    apSmoothJet admissible 1 cell state.1) ∧
  (∀ cell, equivariantAverageJet (apSmoothJet admissible 2 cell (apSmoothPlanar L sigma gamma ell state.2)) =
    apSmoothJet admissible 2 cell (apSmoothPlanar L sigma gamma ell state.2)) ∧
  (∀ cell, angularClosedJet 0 (apSmoothJet admissible 1 cell (apSmoothScalar L sigma gamma ell state.2)) =
    apSmoothJet admissible 1 cell (apSmoothScalar L sigma gamma ell state.2))

theorem meanState_raw (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (raw : IsRawMeanSource admissible source) :
    IsRawMeanState admissible (meanState source) := by
  refine ⟨?_, ?_, ?_⟩
  · intro cell
    change angularClosedJetLinear 1 0 (apSmoothJet admissible 1 cell 0) = apSmoothJet admissible 1 cell 0
    rw [map_zero, map_zero]
  · intro cell
    have planar := congrArg (apSmoothJet admissible 2 cell) (apPlanar_inclusion admissible (meanVector source.1))
    have scaled := (map_smul (apSmoothJet admissible 2 cell) (1 / 2 : ℂ)
      (apSmoothQuarter L sigma gamma ell source.1)).trans
      (congrArg (fun jet : ClosedJet 2 => (1 / 2 : ℂ) • jet)
        (apSmoothValueMap_jet admissible quarterValueMap source.1 cell))
    have law := planar.trans scaled
    have closed : equivariantAverageJet ((1 / 2 : ℂ) • valueMapJet quarterValueMap
        (apSmoothJet admissible 2 cell source.1)) =
        (1 / 2 : ℂ) • valueMapJet quarterValueMap (apSmoothJet admissible 2 cell source.1) := by
      rw [equivariantAverageJet_smul, averageJet_quarter, raw.1 cell]
    exact (congrArg (fun jet : ClosedJet 2 => equivariantAverageJet jet = jet) law).mpr closed
  · intro cell
    have law := (congrArg (apSmoothJet admissible 1 cell) (apScalar_inclusion admissible (meanVector source.1))).trans (map_zero _)
    exact (congrArg (fun jet : ClosedJet 1 => angularClosedJet 0 jet = jet) law).mpr
      (map_zero (angularClosedJetLinear 1 0))

theorem rawCircular_theta_zero (admissible : Admissible L sigma gamma ell)
    (state : circularCompensatedCore admissible) (raw : IsRawMeanState admissible state.val) : state.val.1 = 0 := by
  have meanZero := ((mem_compensatedFlatCore admissible state.val).mp state.property.1).1.1
  apply apSmoothJet_ext admissible
  intro cell
  exact ((raw.1 cell).symm.trans (meanZero cell)).trans (map_zero (apSmoothJet admissible 1 cell)).symm

theorem rawCircular_scalar_zero (admissible : Admissible L sigma gamma ell)
    (state : circularCompensatedCore admissible) (raw : IsRawMeanState admissible state.val) :
    apSmoothScalar L sigma gamma ell state.val.2 = 0 := by
  have mean := (apSmoothScalar_complement admissible state.val.2).symm.trans
    ((congrArg (apSmoothScalar L sigma gamma ell) (circularRemainder_complement_zero admissible state)).trans (map_zero _))
  apply apSmoothJet_ext admissible
  intro cell
  have closed := (apSmoothAngularMean_jet admissible (apSmoothScalar L sigma gamma ell state.val.2) cell).symm.trans
    ((congrArg (apSmoothJet admissible 1 cell) mean).trans (map_zero _))
  exact ((raw.2.2 cell).symm.trans closed).trans (map_zero (apSmoothJet admissible 1 cell)).symm

theorem rawCircular_planar_rotation (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell) (raw : IsRawMeanState admissible state) :
    apSmoothRotation admissible 2 (apSmoothPlanar L sigma gamma ell state.2) =
      apSmoothQuarter L sigma gamma ell (apSmoothPlanar L sigma gamma ell state.2) := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothRotation_jet admissible (apSmoothPlanar L sigma gamma ell state.2) cell).trans
    ((rotationJet_of_equivariant _ (raw.2.1 cell)).trans
      (apSmoothValueMap_jet admissible quarterValueMap (apSmoothPlanar L sigma gamma ell state.2) cell).symm)

private theorem force_inverse_algebra {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (quarter rotation : E →ₗ[ℂ] E) (gradient : F →ₗ[ℂ] E)
    (square : ∀ value, quarter (quarter value) = -value) (theta : F) (vector force : E)
    (thetaZero : theta = 0) (rotates : rotation vector = quarter vector)
    (equation : (-2 : ℂ) • quarter (gradient theta) - (rotation vector + quarter vector) = force) :
    vector = (1 / 2 : ℂ) • quarter force := by
  rw [thetaZero, map_zero, map_zero, smul_zero, rotates] at equation
  have turned := congrArg quarter equation
  rw [map_sub, map_zero, map_add, square] at turned
  calc
    vector = (1 / 2 : ℂ) • (0 - (-vector + -vector)) := by module
    _ = _ := congrArg (fun value : E => (1 / 2 : ℂ) • value) turned

/-- Literal uniqueness in the raw-zero part of the actual circular gauge domain.
The full force row determines the remainder after both original gauges kill Θ and e. -/
theorem meanState_unique (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (state : circularCompensatedCore admissible)
    (raw : IsRawMeanState admissible state.val) (force : circularForce admissible state.val = source.1) :
    state.val = meanState source := by
  have theta := rawCircular_theta_zero admissible state raw
  have scalar := rawCircular_scalar_zero admissible state raw
  have equation := (circularForce_eq_inner admissible state).symm.trans force
  have planar : apSmoothPlanar L sigma gamma ell state.val.2 = meanVector source.1 :=
    force_inverse_algebra (apSmoothQuarter L sigma gamma ell) (apSmoothRotation admissible 2)
      (apSmoothGradient admissible) (apSmoothQuarter_square admissible) state.val.1
      (apSmoothPlanar L sigma gamma ell state.val.2) source.1 theta
      (rawCircular_planar_rotation admissible state.val raw) equation
  apply Prod.ext theta
  have split := (apSmooth_splitting admissible state.val.2).symm
  exact split.trans ((congrArg₂ (fun first second : APSmooth L sigma gamma ell 3 => first + second)
    (congrArg (apSmoothValueMap L sigma gamma ell planarInclusionMap) planar)
    ((congrArg (apSmoothValueMap L sigma gamma ell toroidalInclusionMap) scalar).trans (map_zero _))).trans (add_zero _))

end Grad.ActualMeanInverse
