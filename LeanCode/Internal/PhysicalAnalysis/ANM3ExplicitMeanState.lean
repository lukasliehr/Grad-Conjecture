import ANM2ActualMeanSource

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualMeanInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.NonlinearDivision
variable {L sigma gamma ell : ℝ}

private theorem half_square {E : Type*} [AddCommGroup E] [Module ℂ E]
    (quarter : E →ₗ[ℂ] E) (field : E) (square : quarter (quarter field) = -field) :
    quarter ((1 / 2 : ℂ) • quarter field) = -(1 / 2 : ℂ) • field := by
  rw [map_smul, square, smul_neg, neg_smul]

private theorem half_rotation {E : Type*} [AddCommGroup E] [Module ℂ E]
    (rotation quarter : E →ₗ[ℂ] E) (field : E)
    (commute : rotation (quarter field) = quarter (rotation field))
    (rotates : rotation field = quarter field) (square : quarter (quarter field) = -field) :
    rotation ((1 / 2 : ℂ) • quarter field) = -(1 / 2 : ℂ) • field := by
  rw [map_smul, commute, rotates, square, smul_neg, neg_smul]

private theorem half_tangent {E : Type*} [AddCommGroup E] [Module ℂ E]
    (quarter tangent : E →ₗ[ℂ] E) (field : E)
    (square : ∀ value, quarter (quarter value) = -value)
    (radial : field + quarter (tangent (quarter field)) = field) :
    tangent ((1 / 2 : ℂ) • quarter field) = 0 := by
  have correction := add_eq_left.mp radial
  have twice := congrArg quarter correction
  rw [square, map_zero, neg_eq_zero] at twice
  rw [map_smul, twice, smul_zero]

private theorem mean_force_algebra {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (quarter rotation : E →ₗ[ℂ] E) (gradient : F →ₗ[ℂ] E)
    (field vector : E) (rotates : rotation vector = -(1 / 2 : ℂ) • field)
    (turns : quarter vector = -(1 / 2 : ℂ) • field) :
    (-2 : ℂ) • quarter (gradient 0) - (rotation vector + quarter vector) = field := by
  rw [map_zero, map_zero, smul_zero, rotates, turns]
  module

theorem apPlanar_inclusion (admissible : Admissible L sigma gamma ell) (field : APSmooth L sigma gamma ell 2) :
    apSmoothPlanar L sigma gamma ell (apSmoothValueMap L sigma gamma ell planarInclusionMap field) = field := by
  apply apSmoothJet_ext admissible
  intro cell
  have outer := apSmoothValueMap_jet admissible planarPartMap
    (apSmoothValueMap L sigma gamma ell planarInclusionMap field) cell
  have inner := apSmoothValueMap_jet admissible planarInclusionMap field cell
  have closed : valueMapJet planarPartMap (valueMapJet planarInclusionMap (apSmoothJet admissible 2 cell field)) =
      apSmoothJet admissible 2 cell field := by
    rw [valueMapJet_comp, planarPart_planarInclusion]
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    exact valueMapJet_value _ _ _
  exact outer.trans ((congrArg (valueMapJet planarPartMap) inner).trans closed)

theorem apScalar_inclusion (admissible : Admissible L sigma gamma ell) (field : APSmooth L sigma gamma ell 2) :
    apSmoothScalar L sigma gamma ell (apSmoothValueMap L sigma gamma ell planarInclusionMap field) = 0 := by
  apply apSmoothJet_ext admissible
  intro cell
  have outer := apSmoothValueMap_jet admissible toroidalPartMap
    (apSmoothValueMap L sigma gamma ell planarInclusionMap field) cell
  have inner := apSmoothValueMap_jet admissible planarInclusionMap field cell
  have closed : valueMapJet toroidalPartMap (valueMapJet planarInclusionMap (apSmoothJet admissible 2 cell field)) = 0 := by
    rw [valueMapJet_comp, toroidalPart_planarInclusion, valueMapJet_zero]
  exact outer.trans ((congrArg (valueMapJet toroidalPartMap) inner).trans
    (closed.trans (map_zero (apSmoothJet admissible 1 cell)).symm))

/-- Exact AN26 vector, at every cell and point in the original carrier. -/
def meanVector (field : APSmooth L sigma gamma ell 2) : APSmooth L sigma gamma ell 2 :=
  (1 / 2 : ℂ) • apSmoothQuarter L sigma gamma ell field

def meanState (source : SmoothCapSource L sigma gamma ell) : CompensatedData L sigma gamma ell :=
  (0, apSmoothValueMap L sigma gamma ell planarInclusionMap (meanVector source.1))

theorem meanVector_quarter (admissible : Admissible L sigma gamma ell) (field : APSmooth L sigma gamma ell 2) :
    apSmoothQuarter L sigma gamma ell (meanVector field) = -(1 / 2 : ℂ) • field :=
  half_square (apSmoothQuarter L sigma gamma ell) field (apSmoothQuarter_square admissible field)

theorem meanVector_rotation (admissible : Admissible L sigma gamma ell) (field : APSmooth L sigma gamma ell 2)
    (tangent : apSmoothTangential L sigma gamma ell field = field) :
    apSmoothRotation admissible 2 (meanVector field) = -(1 / 2 : ℂ) • field := by
  have rotation := apSmoothRotation_tangential admissible field
  rw [tangent] at rotation
  exact half_rotation (apSmoothRotation admissible 2) (apSmoothQuarter L sigma gamma ell) field
    (apSmoothRotation_valueMap admissible quarterValueMap field) rotation (apSmoothQuarter_square admissible field)

theorem meanVector_tangent_zero (admissible : Admissible L sigma gamma ell) (field : APSmooth L sigma gamma ell 2)
    (radial : apSmoothQrad L sigma gamma ell field = field) :
    apSmoothTangential L sigma gamma ell (meanVector field) = 0 :=
  half_tangent (apSmoothQuarter L sigma gamma ell) (apSmoothTangential L sigma gamma ell) field
    (apSmoothQuarter_square admissible) radial

theorem meanState_reconstruct (admissible : Admissible L sigma gamma ell) (source : SmoothCapSource L sigma gamma ell) :
    compensatedReconstruct admissible (meanState source) =
      apSmoothValueMap L sigma gamma ell planarInclusionMap (meanVector source.1) := by
  exact (congrArg (fun value => value + apSmoothValueMap L sigma gamma ell planarInclusionMap (meanVector source.1))
    (map_zero (apSmoothCovariant admissible))).trans (zero_add _)

theorem meanState_complement_zero (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible) :
    apSmoothComplement L sigma gamma ell (compensatedReconstruct admissible (meanState source)) = 0 := by
  rw [meanState_reconstruct admissible source]
  let included := apSmoothValueMap L sigma gamma ell planarInclusionMap (meanVector source.1)
  have planar : apSmoothPlanar L sigma gamma ell (apSmoothComplement L sigma gamma ell included) = 0 :=
    (apSmoothPlanar_complement admissible included).trans
      ((congrArg (apSmoothTangential L sigma gamma ell) (apPlanar_inclusion admissible (meanVector source.1))).trans
        (meanVector_tangent_zero admissible source.1 (actualSource_conditions admissible source compatible).1.1))
  have scalar : apSmoothScalar L sigma gamma ell (apSmoothComplement L sigma gamma ell included) = 0 :=
    (apSmoothScalar_complement admissible included).trans
      ((congrArg (apSmoothAngularMean L sigma gamma ell 1) (apScalar_inclusion admissible (meanVector source.1))).trans
        (map_zero (apSmoothAngularMean L sigma gamma ell 1)))
  have split := apSmooth_splitting admissible (apSmoothComplement L sigma gamma ell included)
  have first := (congrArg (apSmoothValueMap L sigma gamma ell planarInclusionMap) planar).trans
    (map_zero (apSmoothValueMap L sigma gamma ell planarInclusionMap))
  have second := (congrArg (apSmoothValueMap L sigma gamma ell toroidalInclusionMap) scalar).trans
    (map_zero (apSmoothValueMap L sigma gamma ell toroidalInclusionMap))
  exact split.symm.trans ((congrArg₂ (fun first second : APSmooth L sigma gamma ell 3 => first + second) first second).trans (zero_add _))

theorem meanState_circularCore (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (raw : IsRawMeanSource admissible source) : meanState source ∈ circularCompensatedCore admissible := by
  have first := meanSource_firstJet_zero admissible source compatible raw
  have turned := apSmoothValueMap_preserves_firstJet admissible quarterValueMap source.1 first
  have scaled : APSmoothAxisFirstJetZero admissible (meanVector source.1) :=
    (mem_apSmoothAxisFirsts admissible _).mp ((apSmoothAxisFirsts admissible 2).smul_mem (1 / 2 : ℂ)
      ((mem_apSmoothAxisFirsts admissible _).mpr turned))
  have total := apSmoothValueMap_preserves_firstJet admissible planarInclusionMap (meanVector source.1) scaled
  refine ⟨(mem_compensatedFlatCore admissible _).mpr ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact (mem_apSmoothMeanFree admissible 0).mp (Submodule.zero_mem _)
  · exact (mem_apSmoothAxisFirsts admissible 0).mp (Submodule.zero_mem _)
  · rw [meanState_reconstruct admissible source]
    exact total
  · exact meanState_complement_zero admissible source compatible

theorem meanState_forceInner (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (raw : IsRawMeanSource admissible source) : circularForceInner admissible (meanState source) = source.1 := by
  change (-2 : ℂ) • apSmoothQuarter L sigma gamma ell (apSmoothGradient admissible 0) -
    (apSmoothRotation admissible 2 (apSmoothPlanar L sigma gamma ell (apSmoothValueMap L sigma gamma ell planarInclusionMap (meanVector source.1))) +
      apSmoothQuarter L sigma gamma ell (apSmoothPlanar L sigma gamma ell (apSmoothValueMap L sigma gamma ell planarInclusionMap (meanVector source.1)))) = _
  exact (congrArg (fun vector : APSmooth L sigma gamma ell 2 =>
      (-2 : ℂ) • apSmoothQuarter L sigma gamma ell (apSmoothGradient admissible 0) -
        (apSmoothRotation admissible 2 vector + apSmoothQuarter L sigma gamma ell vector))
    (apPlanar_inclusion admissible (meanVector source.1))).trans
      (mean_force_algebra (apSmoothQuarter L sigma gamma ell) (apSmoothRotation admissible 2)
        (apSmoothGradient admissible) source.1 (meanVector source.1)
        (meanVector_rotation admissible source.1 (meanSource_tangential admissible source compatible raw))
        (meanVector_quarter admissible source.1))

theorem meanState_force (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (raw : IsRawMeanSource admissible source) : circularForce admissible (meanState source) = source.1 := by
  change apSmoothQrad L sigma gamma ell (circularForceInner admissible (meanState source)) = _
  rw [meanState_forceInner admissible source compatible raw]
  exact (actualSource_conditions admissible source compatible).1.1

theorem meanState_third (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) : circularThird admissible (meanState source) = 0 := by
  change apSmoothRotation admissible 1 (apSmoothScalar L sigma gamma ell
    (apSmoothValueMap L sigma gamma ell planarInclusionMap (meanVector source.1))) = 0
  rw [apScalar_inclusion admissible _, map_zero]

end Grad.ActualMeanInverse
