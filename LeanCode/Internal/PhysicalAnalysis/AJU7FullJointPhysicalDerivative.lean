import AJU6FullMixedSectionDerivatives
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff Interval ENNReal BigOperators
namespace Grad.AnnularPhysicalFourier
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularJointRegularity Grad.AnnularRegularity

local instance : NormedAddCommGroup (ComplexEuclidean 1) := PiLp.normedAddCommGroup 2 (fun _ : Fin 1 => ℂ)
local instance : AddCommGroup (ComplexEuclidean 1) := (PiLp.normedAddCommGroup 2 (fun _ : Fin 1 => ℂ)).toAddCommGroup
local instance : TopologicalSpace (ComplexEuclidean 1) := (PiLp.normedAddCommGroup 2 (fun _ : Fin 1 => ℂ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
local instance : NormedSpace ℝ (ComplexEuclidean 1) := PiLp.normedSpace 2 ℝ (fun _ : Fin 1 => ℂ)
local instance : Module ℝ (ComplexEuclidean 1) := (PiLp.normedSpace 2 ℝ (fun _ : Fin 1 => ℂ)).toModule

/-- The continuous extension is used only to express ordinary derivatives on
an ambient Euclidean space; all physical values are on the original collar. -/
def physicalMixedFourierField (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (jet : PhysicalFourierJet lower positive bounded)
    (radial angular cell : ℕ) (point : ℝ × (ℝ × ℝ)) : ComplexEuclidean 1 :=
  physicalMixedFourierSection lower positive bounded jet radial angular cell point.2
    (radialClamp lower bounded.le point.1)

section Derivatives
variable (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (jet : PhysicalFourierJet lower positive bounded)

theorem physicalMixedFourierField_continuous (radial angular cell : ℕ) :
    Continuous (physicalMixedFourierField lower positive bounded jet radial angular cell) := by
  change Continuous (fun point : ℝ × (ℝ × ℝ) =>
    physicalMixedFourierSection lower positive bounded jet radial angular cell point.2
      (radialClamp lower bounded.le point.1))
  exact continuous_eval.comp
    (((physicalMixedFourierSection_continuous lower positive bounded jet radial angular cell).comp
      continuous_snd).prodMk ((radialClamp_continuous lower bounded.le).comp continuous_fst))

theorem physicalMixedFourierField_radial (radial angular cell : ℕ)
    (radius : ℝ) (inside : radius ∈ Ioo lower 1) (angles : ℝ × ℝ) :
    HasDerivAt (fun r => physicalMixedFourierField lower positive bounded jet radial angular cell (r, angles))
      (physicalMixedFourierField lower positive bounded jet (radial + 1) angular cell (radius, angles)) radius := by
  have law := (physicalMixedFourierSection_radialDerivative lower positive bounded jet
    radial angular cell angles radius ⟨inside.1.le, inside.2.le⟩).hasDerivAt (Icc_mem_nhds inside.1 inside.2)
  change HasDerivAt (radialSectionExtension 1 lower bounded.le
    (physicalMixedFourierSection lower positive bounded jet radial angular cell angles)) _ radius
  rw [physicalMixedFourierField, radialClamp_eq lower bounded.le radius ⟨inside.1.le, inside.2.le⟩]
  exact law

theorem physicalMixedFourierField_angular (radial angular cell : ℕ) (radius polar axial : ℝ) :
    HasDerivAt (fun angle => physicalMixedFourierField lower positive bounded jet radial angular cell (radius, angle, axial))
      (physicalMixedFourierField lower positive bounded jet radial (angular + 1) cell (radius, polar, axial)) polar :=
  physicalMixedFourierValue_angular lower positive bounded jet radial angular cell
    (radialClamp lower bounded.le radius) polar axial

theorem physicalMixedFourierField_cell (radial angular cell : ℕ) (radius polar axial : ℝ) :
    HasDerivAt (fun angle => physicalMixedFourierField lower positive bounded jet radial angular cell (radius, polar, angle))
      (physicalMixedFourierField lower positive bounded jet radial angular (cell + 1) (radius, polar, axial)) axial :=
  physicalMixedFourierValue_cell lower positive bounded jet radial angular cell
    (radialClamp lower bounded.le radius) polar axial

/-- The actual two tangential partials give the genuine joint tangential
Fréchet derivative, including at either radial endpoint. -/
theorem physicalMixedFourierField_angles (radial angular cell : ℕ) (radius : ℝ) (angles : ℝ × ℝ) :
    HasFDerivAt (fun pair => physicalMixedFourierField lower positive bounded jet radial angular cell (radius, pair))
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (physicalMixedFourierField lower positive bounded jet radial (angular + 1) cell (radius, angles))).coprod
       (ContinuousLinearMap.toSpanSingleton ℝ
        (physicalMixedFourierField lower positive bounded jet radial angular (cell + 1) (radius, angles)))) angles := by
  apply HasStrictFDerivAt.hasFDerivAt
  apply hasStrictFDerivAt_uncurry_coprod
    (f := fun polar axial => physicalMixedFourierField lower positive bounded jet radial angular cell (radius, polar, axial))
    (f₁ := fun polar axial => ContinuousLinearMap.toSpanSingleton ℝ
      (physicalMixedFourierField lower positive bounded jet radial (angular + 1) cell (radius, polar, axial)))
    (f₂ := fun polar axial => ContinuousLinearMap.toSpanSingleton ℝ
      (physicalMixedFourierField lower positive bounded jet radial angular (cell + 1) (radius, polar, axial)))
  · exact Filter.Eventually.of_forall (fun point =>
      (physicalMixedFourierField_angular lower positive bounded jet radial angular cell radius point.1 point.2).hasFDerivAt)
  · exact Filter.Eventually.of_forall (fun point =>
      (physicalMixedFourierField_cell lower positive bounded jet radial angular cell radius point.1 point.2).hasFDerivAt)
  · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ (ComplexEuclidean 1)).continuous.comp
      ((physicalMixedFourierField_continuous lower positive bounded jet radial (angular + 1) cell).comp
        (continuous_const.prodMk continuous_id))).continuousAt
  · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ (ComplexEuclidean 1)).continuous.comp
      ((physicalMixedFourierField_continuous lower positive bounded jet radial angular (cell + 1)).comp
        (continuous_const.prodMk continuous_id))).continuousAt

/-- All three literal physical partials assemble to the actual joint
Fréchet derivative in the collar interior. -/
theorem physicalMixedFourierField_hasFDerivAt (radial angular cell : ℕ)
    (point : ℝ × (ℝ × ℝ)) (inside : point.1 ∈ Ioo lower 1) :
    HasFDerivAt (physicalMixedFourierField lower positive bounded jet radial angular cell)
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (physicalMixedFourierField lower positive bounded jet (radial + 1) angular cell point)).coprod
       ((ContinuousLinearMap.toSpanSingleton ℝ
        (physicalMixedFourierField lower positive bounded jet radial (angular + 1) cell point)).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ
        (physicalMixedFourierField lower positive bounded jet radial angular (cell + 1) point)))) point := by
  apply HasStrictFDerivAt.hasFDerivAt
  apply hasStrictFDerivAt_uncurry_coprod
    (f := fun radius angles => physicalMixedFourierField lower positive bounded jet radial angular cell (radius, angles))
    (f₁ := fun radius angles => ContinuousLinearMap.toSpanSingleton ℝ
      (physicalMixedFourierField lower positive bounded jet (radial + 1) angular cell (radius, angles)))
    (f₂ := fun radius angles => (ContinuousLinearMap.toSpanSingleton ℝ
      (physicalMixedFourierField lower positive bounded jet radial (angular + 1) cell (radius, angles))).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ
      (physicalMixedFourierField lower positive bounded jet radial angular (cell + 1) (radius, angles))))
  · filter_upwards [(isOpen_Ioo.preimage continuous_fst).mem_nhds inside] with nearby member
    exact (physicalMixedFourierField_radial lower positive bounded jet radial angular cell nearby.1 member nearby.2).hasFDerivAt
  · exact Filter.Eventually.of_forall (fun nearby =>
      physicalMixedFourierField_angles lower positive bounded jet radial angular cell nearby.1 nearby.2)
  · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ (ComplexEuclidean 1)).continuous.comp
      (physicalMixedFourierField_continuous lower positive bounded jet (radial + 1) angular cell)).continuousAt
  · exact (((ContinuousLinearMap.toSpanSingletonLIE ℝ (ComplexEuclidean 1)).continuous.comp
      (physicalMixedFourierField_continuous lower positive bounded jet radial (angular + 1) cell)).continuousLinearMapCoprod
      ((ContinuousLinearMap.toSpanSingletonLIE ℝ (ComplexEuclidean 1)).continuous.comp
      (physicalMixedFourierField_continuous lower positive bounded jet radial angular (cell + 1)))).continuousAt

end Derivatives
end Grad.AnnularPhysicalFourier
