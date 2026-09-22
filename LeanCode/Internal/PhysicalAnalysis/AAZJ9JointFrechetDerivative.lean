import AAZJ8AllMixedSectionDerivatives
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularJointRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularRadialJets Grad.AnnularRegularity

local instance : NormedAddCommGroup (ComplexEuclidean 1) := PiLp.normedAddCommGroup 2 (fun _ : Fin 1 => ℂ)
local instance : AddCommGroup (ComplexEuclidean 1) := (PiLp.normedAddCommGroup 2 (fun _ : Fin 1 => ℂ)).toAddCommGroup
local instance : TopologicalSpace (ComplexEuclidean 1) := (PiLp.normedAddCommGroup 2 (fun _ : Fin 1 => ℂ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
local instance : NormedSpace ℝ (ComplexEuclidean 1) := PiLp.normedSpace 2 ℝ (fun _ : Fin 1 => ℂ)
local instance : Module ℝ (ComplexEuclidean 1) := (PiLp.normedSpace 2 ℝ (fun _ : Fin 1 => ℂ)).toModule

/-- The continuous extension is used only to express ordinary derivatives on
an ambient Euclidean space; all physical values are on the original collar. -/
def annularMixedFourierField (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (jet : ℕ → AnnularRawFamily lower)
    (weak : ∀ order, AnnularPhysicalWeakDerivative parameters lower positive (jet order) (jet (order + 1)))
    (radial angular cell : ℕ) (point : ℝ × (ℝ × ℝ)) : ComplexEuclidean 1 :=
  annularMixedFourierSection parameters lower positive bounded jet weak radial angular cell point.2
    (radialClamp lower bounded.le point.1)

section Derivatives
variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (jet : ℕ → AnnularRawFamily lower)
    (weak : ∀ order, AnnularPhysicalWeakDerivative parameters lower positive (jet order) (jet (order + 1)))
    (grades : ∀ order grade, HasAnnularRawGrade lower grade (jet order))
include grades

theorem annularMixedFourierField_continuous (radial angular cell : ℕ) :
    Continuous (annularMixedFourierField parameters lower positive bounded jet weak radial angular cell) := by
  change Continuous (fun point : ℝ × (ℝ × ℝ) =>
    annularMixedFourierSection parameters lower positive bounded jet weak radial angular cell point.2
      (radialClamp lower bounded.le point.1))
  exact continuous_eval.comp
    (((annularMixedFourierSection_continuous parameters lower positive bounded jet weak grades radial angular cell).comp
      continuous_snd).prodMk ((radialClamp_continuous lower bounded.le).comp continuous_fst))

theorem annularMixedFourierField_radial (radial angular cell : ℕ)
    (radius : ℝ) (inside : radius ∈ Ioo lower 1) (angles : ℝ × ℝ) :
    HasDerivAt (fun r => annularMixedFourierField parameters lower positive bounded jet weak radial angular cell (r, angles))
      (annularMixedFourierField parameters lower positive bounded jet weak (radial + 1) angular cell (radius, angles)) radius := by
  have law := (annularMixedFourierSection_radialDerivative parameters lower positive bounded jet weak grades
    radial angular cell angles radius ⟨inside.1.le, inside.2.le⟩).hasDerivAt (Icc_mem_nhds inside.1 inside.2)
  change HasDerivAt (radialSectionExtension 1 lower bounded.le
    (annularMixedFourierSection parameters lower positive bounded jet weak radial angular cell angles)) _ radius
  rw [annularMixedFourierField, radialClamp_eq lower bounded.le radius ⟨inside.1.le, inside.2.le⟩]
  exact law

theorem annularMixedFourierField_angular (radial angular cell : ℕ) (radius polar axial : ℝ) :
    HasDerivAt (fun angle => annularMixedFourierField parameters lower positive bounded jet weak radial angular cell (radius, angle, axial))
      (annularMixedFourierField parameters lower positive bounded jet weak radial (angular + 1) cell (radius, polar, axial)) polar :=
  annularMixedFourierValue_angular parameters lower positive bounded jet weak grades radial angular cell
    (radialClamp lower bounded.le radius) polar axial

theorem annularMixedFourierField_cell (radial angular cell : ℕ) (radius polar axial : ℝ) :
    HasDerivAt (fun angle => annularMixedFourierField parameters lower positive bounded jet weak radial angular cell (radius, polar, angle))
      (annularMixedFourierField parameters lower positive bounded jet weak radial angular (cell + 1) (radius, polar, axial)) axial :=
  annularMixedFourierValue_cell parameters lower positive bounded jet weak grades radial angular cell
    (radialClamp lower bounded.le radius) polar axial

/-- The actual two tangential partials give the genuine joint tangential
Fréchet derivative, including at either radial endpoint. -/
theorem annularMixedFourierField_angles (radial angular cell : ℕ) (radius : ℝ) (angles : ℝ × ℝ) :
    HasFDerivAt (fun pair => annularMixedFourierField parameters lower positive bounded jet weak radial angular cell (radius, pair))
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (annularMixedFourierField parameters lower positive bounded jet weak radial (angular + 1) cell (radius, angles))).coprod
       (ContinuousLinearMap.toSpanSingleton ℝ
        (annularMixedFourierField parameters lower positive bounded jet weak radial angular (cell + 1) (radius, angles)))) angles := by
  apply HasStrictFDerivAt.hasFDerivAt
  apply hasStrictFDerivAt_uncurry_coprod
    (f := fun polar axial => annularMixedFourierField parameters lower positive bounded jet weak radial angular cell (radius, polar, axial))
    (f₁ := fun polar axial => ContinuousLinearMap.toSpanSingleton ℝ
      (annularMixedFourierField parameters lower positive bounded jet weak radial (angular + 1) cell (radius, polar, axial)))
    (f₂ := fun polar axial => ContinuousLinearMap.toSpanSingleton ℝ
      (annularMixedFourierField parameters lower positive bounded jet weak radial angular (cell + 1) (radius, polar, axial)))
  · exact Filter.Eventually.of_forall (fun point =>
      (annularMixedFourierField_angular parameters lower positive bounded jet weak grades radial angular cell radius point.1 point.2).hasFDerivAt)
  · exact Filter.Eventually.of_forall (fun point =>
      (annularMixedFourierField_cell parameters lower positive bounded jet weak grades radial angular cell radius point.1 point.2).hasFDerivAt)
  · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ (ComplexEuclidean 1)).continuous.comp
      ((annularMixedFourierField_continuous parameters lower positive bounded jet weak grades radial (angular + 1) cell).comp
        (continuous_const.prodMk continuous_id))).continuousAt
  · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ (ComplexEuclidean 1)).continuous.comp
      ((annularMixedFourierField_continuous parameters lower positive bounded jet weak grades radial angular (cell + 1)).comp
        (continuous_const.prodMk continuous_id))).continuousAt

/-- All three literal physical partials assemble to the actual joint
Fréchet derivative in the collar interior. -/
theorem annularMixedFourierField_hasFDerivAt (radial angular cell : ℕ)
    (point : ℝ × (ℝ × ℝ)) (inside : point.1 ∈ Ioo lower 1) :
    HasFDerivAt (annularMixedFourierField parameters lower positive bounded jet weak radial angular cell)
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (annularMixedFourierField parameters lower positive bounded jet weak (radial + 1) angular cell point)).coprod
       ((ContinuousLinearMap.toSpanSingleton ℝ
        (annularMixedFourierField parameters lower positive bounded jet weak radial (angular + 1) cell point)).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ
        (annularMixedFourierField parameters lower positive bounded jet weak radial angular (cell + 1) point)))) point := by
  apply HasStrictFDerivAt.hasFDerivAt
  apply hasStrictFDerivAt_uncurry_coprod
    (f := fun radius angles => annularMixedFourierField parameters lower positive bounded jet weak radial angular cell (radius, angles))
    (f₁ := fun radius angles => ContinuousLinearMap.toSpanSingleton ℝ
      (annularMixedFourierField parameters lower positive bounded jet weak (radial + 1) angular cell (radius, angles)))
    (f₂ := fun radius angles => (ContinuousLinearMap.toSpanSingleton ℝ
      (annularMixedFourierField parameters lower positive bounded jet weak radial (angular + 1) cell (radius, angles))).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ
      (annularMixedFourierField parameters lower positive bounded jet weak radial angular (cell + 1) (radius, angles))))
  · filter_upwards [(isOpen_Ioo.preimage continuous_fst).mem_nhds inside] with nearby member
    exact (annularMixedFourierField_radial parameters lower positive bounded jet weak grades radial angular cell nearby.1 member nearby.2).hasFDerivAt
  · exact Filter.Eventually.of_forall (fun nearby =>
      annularMixedFourierField_angles parameters lower positive bounded jet weak grades radial angular cell nearby.1 nearby.2)
  · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ (ComplexEuclidean 1)).continuous.comp
      (annularMixedFourierField_continuous parameters lower positive bounded jet weak grades (radial + 1) angular cell)).continuousAt
  · exact (((ContinuousLinearMap.toSpanSingletonLIE ℝ (ComplexEuclidean 1)).continuous.comp
      (annularMixedFourierField_continuous parameters lower positive bounded jet weak grades radial (angular + 1) cell)).continuousLinearMapCoprod
      ((ContinuousLinearMap.toSpanSingletonLIE ℝ (ComplexEuclidean 1)).continuous.comp
      (annularMixedFourierField_continuous parameters lower positive bounded jet weak grades radial angular (cell + 1)))).continuousAt

end Derivatives
end Grad.AnnularJointRegularity
