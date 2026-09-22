import SCD15CoefficientLinearity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial Grad.BoundaryTrace

/-- Isometric coordinates for radial L2(r dr): store sqrt(r) times the
coefficient in ordinary L2(dr). The norm identity below retains literal r dr. -/
abbrev RadialL2 (dimension : ℕ) (lower : ℝ) :=
  Lp (ComplexEuclidean dimension) 2 (volume.restrict (Icc lower 1))

theorem radial_weighted_memLp {dimension : ℕ} (lower : ℝ)
    (field : ℝ → ComplexEuclidean dimension) (continuousField : Continuous field) :
    MemLp (fun radius => Real.sqrt radius • field radius) 2 (volume.restrict (Icc lower 1)) := by
  let : IsFiniteMeasure (volume.restrict (Icc lower (1 : ℝ))) := by
    rw [isFiniteMeasure_restrict]
    exact isCompact_Icc.measure_ne_top
  have continuousWeighted : Continuous (fun radius => Real.sqrt radius • field radius) :=
    Real.continuous_sqrt.smul continuousField
  obtain ⟨bound, bounded⟩ := isCompact_Icc.exists_bound_of_continuousOn continuousWeighted.continuousOn
  apply MemLp.of_bound continuousWeighted.aestronglyMeasurable bound
  filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
  exact bounded radius inside

def radialToLp {dimension : ℕ} (lower : ℝ)
    (field : ℝ → ComplexEuclidean dimension) (continuousField : Continuous field) : RadialL2 dimension lower :=
  (radial_weighted_memLp lower field continuousField).toLp (fun radius => Real.sqrt radius • field radius)

theorem radialToLp_ae {dimension : ℕ} (lower : ℝ)
    (field : ℝ → ComplexEuclidean dimension) (continuousField : Continuous field) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      radialToLp lower field continuousField radius = Real.sqrt radius • field radius :=
  (radial_weighted_memLp lower field continuousField).coeFn_toLp

theorem radialLp_norm_sq {dimension : ℕ} (lower : ℝ) (field : RadialL2 dimension lower) :
    ‖field‖ ^ 2 = ∫ radius : ℝ, ‖field radius‖ ^ 2 ∂volume.restrict (Icc lower 1) := by
  let := InnerProductSpace.rclikeToReal ℂ (ComplexEuclidean dimension)
  calc
    _ = inner ℝ field field := (real_inner_self_eq_norm_sq field).symm
    _ = ∫ radius : ℝ, inner ℝ (field radius) (field radius) ∂volume.restrict (Icc lower 1) :=
      L2.inner_def (𝕜 := ℝ) field field
    _ = _ := by simp only [real_inner_self_eq_norm_sq]

theorem radialToLp_norm_sq {dimension : ℕ} (lower : ℝ)
    (nonnegative : 0 ≤ lower) (bounded : lower ≤ 1)
    (field : ℝ → ComplexEuclidean dimension) (continuousField : Continuous field) :
    ‖radialToLp lower field continuousField‖ ^ 2 =
      ∫ radius in lower..1, radius * ‖field radius‖ ^ 2 := by
  rw [radialLp_norm_sq, intervalIntegral.integral_of_le bounded, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [radialToLp_ae lower field continuousField, ae_restrict_mem measurableSet_Icc]
    with radius literal inside
  rw [literal, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt (nonnegative.trans inside.1)]

theorem annular_interior_ae (lower : ℝ) (positive : 0 < lower) :
    ∀ᵐ radius : ℝ ∂volume.restrict (Icc lower 1), radius ∈ Ioo (0 : ℝ) 1 := by
  have notEndpoint : ∀ᵐ radius : ℝ ∂volume.restrict (Icc lower 1), radius ≠ 1 := by
    rw [ae_iff]
    simp
  filter_upwards [ae_restrict_mem measurableSet_Icc, notEndpoint] with radius inside notOne
  exact ⟨positive.trans_le inside.1, lt_of_le_of_ne inside.2 notOne⟩

theorem radialToLp_add_of_interior {dimension : ℕ} (lower : ℝ) (positive : 0 < lower)
    (first second total : ℝ → ComplexEuclidean dimension)
    (firstContinuous : Continuous first) (secondContinuous : Continuous second) (totalContinuous : Continuous total)
    (literal : ∀ radius ∈ Ioo (0 : ℝ) 1, total radius = first radius + second radius) :
    radialToLp lower total totalContinuous =
      radialToLp lower first firstContinuous + radialToLp lower second secondContinuous := by
  apply Lp.ext
  filter_upwards [radialToLp_ae lower first firstContinuous, radialToLp_ae lower second secondContinuous,
    radialToLp_ae lower total totalContinuous, annular_interior_ae lower positive,
    Lp.coeFn_add (radialToLp lower first firstContinuous) (radialToLp lower second secondContinuous)]
    with radius firstLaw secondLaw totalLaw inside additive
  rw [totalLaw, additive, Pi.add_apply, firstLaw, secondLaw, literal radius inside, smul_add]

theorem radialToLp_smul_of_interior {dimension : ℕ} (lower : ℝ) (positive : 0 < lower)
    (scalar : ℂ) (field total : ℝ → ComplexEuclidean dimension)
    (continuousField : Continuous field) (totalContinuous : Continuous total)
    (literal : ∀ radius ∈ Ioo (0 : ℝ) 1, total radius = scalar • field radius) :
    radialToLp lower total totalContinuous = scalar • radialToLp lower field continuousField := by
  apply Lp.ext
  filter_upwards [radialToLp_ae lower field continuousField, radialToLp_ae lower total totalContinuous,
    annular_interior_ae lower positive, Lp.coeFn_smul scalar (radialToLp lower field continuousField)]
    with radius fieldLaw totalLaw inside scaled
  rw [totalLaw, scaled, Pi.smul_apply, fieldLaw, literal radius inside]
  exact smul_comm _ _ _

end Grad.SourceCollarDivision
