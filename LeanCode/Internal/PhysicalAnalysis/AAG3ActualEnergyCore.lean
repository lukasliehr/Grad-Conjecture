import AAG2ComplexSmoothCore
import GQD1GraphClosure

noncomputable section

set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularVariational

open Grad.ClosedJets Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.Compensated

abbrev HighAnnularMode := {pair : ℤ × ℤ // 3 ≤ |pair.1|}

/-- A continuous extension used only to store the literal potential on [a,1]. -/
def annularPotentialWeight (lower length : ℝ) (positive : 0 < lower) (mode cell : ℤ) : C(ℝ, ℝ) :=
  ⟨fun radius => Real.sqrt (annularPotential length (max lower radius) mode cell), by
    apply Real.continuous_sqrt.comp
    exact (continuous_const.div ((continuous_const.max continuous_id).pow 2)
      (fun radius => (sq_pos_of_pos (positive.trans_le (le_max_left _ _))).ne')).add continuous_const⟩

theorem annularPotentialWeight_sq (lower length : ℝ) (positive : 0 < lower)
    (mode cell : ℤ) (radius : ℝ) (inside : lower ≤ radius) :
    annularPotentialWeight lower length positive mode cell radius ^ 2 =
      annularPotential length radius mode cell := by
  change Real.sqrt (annularPotential length (max lower radius) mode cell) ^ 2 = _
  rw [max_eq_right inside, Real.sq_sqrt]
  unfold annularPotential
  exact add_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))
    (div_nonneg (mul_nonneg (highMultiplier_nonnegative _) (sq_nonneg _)) (sq_nonneg _))

abbrev AnnularModeEnergyAmbient (lower : ℝ) :=
  WithLp 2 (RadialL2 1 lower × WithLp 2 (RadialL2 1 lower × ComplexEuclidean 1))

def annularModeEnergyCore (lower length : ℝ) (positive : 0 < lower) (mode cell : ℤ) :
    complexSmoothRadialCore 1 →ₗ[ℂ] AnnularModeEnergyAmbient lower :=
  hilbertPairLinear ((weightedCurveComplex 1 lower).comp (complexCoreSlope 1))
    (hilbertPairLinear
      ((weightedCurveComplex 1 lower).comp
        ((continuousCurveWeight 1 (annularPotentialWeight lower length positive mode cell)).comp
          (complexCoreValue 1)))
      ((Real.sqrt 2 : ℂ) • complexCoreEndpoint 1 1))

theorem annularModeEnergyCore_norm_sq (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (mode cell : ℤ) (core : complexSmoothRadialCore 1) :
    ‖annularModeEnergyCore lower length positive mode cell core‖ ^ 2 =
      (∫ radius in lower..1, radius * (‖core.val.2 radius‖ ^ 2 +
        annularPotential length radius mode cell * ‖core.val.1 radius‖ ^ 2)) +
      2 * ‖core.val.1 1‖ ^ 2 := by
  let weight := annularPotentialWeight lower length positive mode cell
  let curve : C(ℝ, ComplexEuclidean 1) := continuousCurveWeight 1 weight core.val.1
  have outer := WithLp.prod_norm_sq_eq_of_L2 (annularModeEnergyCore lower length positive mode cell core)
  change ‖annularModeEnergyCore lower length positive mode cell core‖ ^ 2 =
    ‖radialToLp lower core.val.2 core.val.2.continuous‖ ^ 2 +
      ‖WithLp.toLp 2 (radialToLp lower curve curve.continuous, (Real.sqrt 2 : ℂ) • core.val.1 1)‖ ^ 2 at outer
  rw [outer, WithLp.prod_norm_sq_eq_of_L2]
  change ‖radialToLp lower core.val.2 core.val.2.continuous‖ ^ 2 +
    (‖radialToLp lower curve curve.continuous‖ ^ 2 + ‖(Real.sqrt 2 : ℂ) • core.val.1 1‖ ^ 2) = _
  rw [radialToLp_norm_sq lower positive.le bounded, radialToLp_norm_sq lower positive.le bounded,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have mass : (∫ radius in lower..1, radius * ‖curve radius‖ ^ 2) =
      ∫ radius in lower..1, radius * (annularPotential length radius mode cell * ‖core.val.1 radius‖ ^ 2) := by
    apply intervalIntegral.integral_congr
    intro radius inside
    have inside' : lower ≤ radius := (min_eq_left bounded).symm.le.trans inside.1
    change radius * ‖weight radius • core.val.1 radius‖ ^ 2 = _
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, annularPotentialWeight_sq _ _ _ _ _ _ inside']
  rw [mass, ← add_assoc, ← intervalIntegral.integral_add]
  · congr 1
    apply intervalIntegral.integral_congr
    intro radius _
    ring
  · exact (continuous_id.mul (core.val.2.continuous.norm.pow 2)).intervalIntegrable lower 1
  · have equality : Set.EqOn (fun radius => radius *
        (annularPotential length radius mode cell * ‖core.val.1 radius‖ ^ 2))
        (fun radius => radius * ‖curve radius‖ ^ 2) (Set.uIcc lower 1) := by
      intro radius inside
      have inside' : lower ≤ radius := (min_eq_left bounded).symm.le.trans inside.1
      change _ = radius * ‖weight radius • core.val.1 radius‖ ^ 2
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, annularPotentialWeight_sq _ _ _ _ _ _ inside']
    exact ((continuous_id.mul (curve.continuous.norm.pow 2)).intervalIntegrable lower 1).congr
      (fun radius inside => (equality (Set.uIoc_subset_uIcc inside)).symm)

abbrev AnnularEnergyAmbient (lower : ℝ) := lp (fun _ : HighAnnularMode => AnnularModeEnergyAmbient lower) 2

def finiteAnnularEnergyCore (lower length : ℝ) (positive : 0 < lower) :
    (HighAnnularMode →₀ complexSmoothRadialCore 1) →ₗ[ℂ] AnnularEnergyAmbient lower :=
  Finsupp.lsum ℂ (fun mode =>
    (lp.singleContinuousLinearMap ℂ (fun _ : HighAnnularMode => AnnularModeEnergyAmbient lower) 2 mode).toLinearMap.comp
      (annularModeEnergyCore lower length positive mode.val.1 mode.val.2))

/-- W in AG7: closure of the actual finite high Fourier smooth graphs in
the exact derivative/potential/outer-value Hilbert coordinates. -/
def annularEnergySpace (lower length : ℝ) (positive : 0 < lower) : Submodule ℂ (AnnularEnergyAmbient lower) :=
  (LinearMap.range (finiteAnnularEnergyCore lower length positive)).topologicalClosure

instance annularEnergySpace_complete (lower length : ℝ) (positive : 0 < lower) :
    CompleteSpace (annularEnergySpace lower length positive) :=
  (LinearMap.range (finiteAnnularEnergyCore lower length positive)).isClosed_topologicalClosure.completeSpace_coe

def annularEnergyCoreInto (lower length : ℝ) (positive : 0 < lower) :
    (HighAnnularMode →₀ complexSmoothRadialCore 1) →ₗ[ℂ] annularEnergySpace lower length positive :=
  (finiteAnnularEnergyCore lower length positive).codRestrict _
    (fun core => Submodule.le_topologicalClosure _ ⟨core, rfl⟩)

theorem annularEnergyCoreInto_denseRange (lower length : ℝ) (positive : 0 < lower) :
    DenseRange (annularEnergyCoreInto lower length positive) :=
by
  let source := LinearMap.range (finiteAnnularEnergyCore lower length positive)
  have dense : DenseRange (Set.inclusion (Submodule.le_topologicalClosure source)) :=
    (denseRange_inclusion_iff _).2 (fun _ member => member)
  apply dense.mono
  rintro _ ⟨point, rfl⟩
  rcases point.property with ⟨core, equality⟩
  exact ⟨core, Subtype.ext equality⟩

end Grad.AnnularVariational
