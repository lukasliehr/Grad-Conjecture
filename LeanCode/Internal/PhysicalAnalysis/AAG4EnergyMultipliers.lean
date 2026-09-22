import AAG3ActualEnergyCore
import ASG7FourierTraceOperators

noncomputable section
set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularVariational

open Grad.ClosedJets Grad.CartesianState Grad.AnnularSourceGraph Grad.SourceCollarDivision
open Grad.CircularHighWeak Grad.MatrixMultiplier

section ComplexLift
variable {Index E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Complex scalar adapter for the accepted uniform lp map construction. -/
def complexLpTwoMap (family : Index → E →L[ℂ] F) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ index value, ‖family index value‖ ≤ constant * ‖value‖) :
    lp (fun _ : Index => E) 2 →L[ℂ] lp (fun _ : Index => F) 2 :=
  let linear : lp (fun _ : Index => E) 2 →ₗ[ℂ] lp (fun _ : Index => F) 2 :=
    { toFun := lpTwoMap (fun index => (family index).restrictScalars ℝ) constant nonnegative bounded
      map_add' := (lpTwoMap (fun index => (family index).restrictScalars ℝ) constant nonnegative bounded).map_add
      map_smul' := by
        intro scalar field
        apply Subtype.ext
        funext index
        exact (family index).map_smul scalar (field index) }
  linear.mkContinuous constant (lpTwoMap_bound (fun index => (family index).restrictScalars ℝ)
    constant nonnegative bounded)

theorem complexLpTwoMap_apply (family : Index → E →L[ℂ] F) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ index value, ‖family index value‖ ≤ constant * ‖value‖)
    (field : lp (fun _ : Index => E) 2) (index : Index) :
    complexLpTwoMap family constant nonnegative bounded field index = family index (field index) := rfl

theorem complexLpTwoMap_bound (family : Index → E →L[ℂ] F) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ index value, ‖family index value‖ ≤ constant * ‖value‖)
    (field : lp (fun _ : Index => E) 2) :
    ‖complexLpTwoMap family constant nonnegative bounded field‖ ≤ constant * ‖field‖ :=
  lpTwoMap_bound (fun index => (family index).restrictScalars ℝ) constant nonnegative bounded field
end ComplexLift

def scalarRadialCoefficient (coefficient : C(ℝ, ℝ)) (radius : ℝ) :
    ComplexEuclidean 1 →L[ℂ] ComplexEuclidean 1 :=
  coefficient radius • ContinuousLinearMap.id ℂ (ComplexEuclidean 1)

theorem scalarRadialCoefficient_bound (lower : ℝ) (coefficient : C(ℝ, ℝ)) (bound : ℝ)
    (bounded : ∀ radius ∈ Icc lower 1, |coefficient radius| ≤ bound) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ‖scalarRadialCoefficient coefficient radius‖ ≤ bound := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
  calc
    _ ≤ ‖coefficient radius‖ * ‖ContinuousLinearMap.id ℂ (ComplexEuclidean 1)‖ := norm_smul_le _ _
    _ ≤ |coefficient radius| * 1 :=
      mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
    _ ≤ bound := by simpa only [mul_one] using bounded radius inside

def scalarRadialMap (lower : ℝ) (coefficient : C(ℝ, ℝ)) (bound : ℝ)
    (bounded : ∀ radius ∈ Icc lower 1, |coefficient radius| ≤ bound) :
    RadialL2 1 lower →L[ℂ] RadialL2 1 lower :=
  matrixMultiplier (volume.restrict (Icc lower 1)) (scalarRadialCoefficient coefficient) bound
    (coefficient.continuous.smul continuous_const).aestronglyMeasurable
    (scalarRadialCoefficient_bound lower coefficient bound bounded)

theorem scalarRadialMap_bound (lower : ℝ) (coefficient : C(ℝ, ℝ)) (bound : ℝ)
    (bounded : ∀ radius ∈ Icc lower 1, |coefficient radius| ≤ bound) (field : RadialL2 1 lower) :
    ‖scalarRadialMap lower coefficient bound bounded field‖ ≤ bound * ‖field‖ :=
  norm_matrixMultiplier_apply_le _ _ _ _ _ field

theorem scalarRadialMap_ae (lower : ℝ) (coefficient : C(ℝ, ℝ)) (bound : ℝ)
    (bounded : ∀ radius ∈ Icc lower 1, |coefficient radius| ≤ bound) (field : RadialL2 1 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      scalarRadialMap lower coefficient bound bounded field radius = coefficient radius • field radius :=
  matrixMultiplier_apply_ae _ _ _ _ _ field

theorem annularPotential_pos (length radius : ℝ) (mode cell : ℤ)
    (high : 3 ≤ |mode|) (positive : 0 < radius) : 0 < annularPotential length radius mode cell := by
  have modeBound : (3 : ℝ) ≤ |(mode : ℝ)| := by exact_mod_cast high
  have modeSq : 0 < (mode : ℝ) ^ 2 := by nlinarith [sq_abs (mode : ℝ)]
  exact add_pos_of_pos_of_nonneg (div_pos modeSq (sq_pos_of_pos positive))
    (div_nonneg (mul_nonneg (highMultiplier_nonnegative _) (sq_nonneg _)) (sq_nonneg _))

theorem annularPotentialWeight_pos (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (radius : ℝ) :
    0 < annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius :=
  Real.sqrt_pos.mpr (annularPotential_pos _ _ _ _ mode.property (positive.trans_le (le_max_left _ _)))

theorem annularPhaseSlope_continuous (parameters : PhaseParameters) (cell : ℤ) :
    Continuous (annularPhaseSlope parameters cell) := by
  have same : annularPhaseSlope parameters cell = deriv (fun radius => Grad.PhaseAlgebra.radialPhase parameters radius cell) := by
    funext radius
    exact (radialPhase_hasDerivAt parameters cell radius).deriv.symm
  rw [same]
  exact (contDiff_infty_iff_deriv.mp (radialPhase_smooth parameters cell)).2.continuous

def annularPhaseMassRatio (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) : C(ℝ, ℝ) :=
  ⟨fun radius => annularPhaseSlope parameters mode.val.2 radius /
    annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius,
    (annularPhaseSlope_continuous parameters mode.val.2).div
      (annularPotentialWeight lower length positive mode.val.1 mode.val.2).continuous
      (fun radius => (annularPotentialWeight_pos lower length positive mode radius).ne')⟩

theorem annularPhaseMassRatio_bound (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)) (mode : HighAnnularMode)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |annularPhaseMassRatio parameters lower length positive mode radius| ≤ 1 / 2 := by
  have rootPositive := annularPotentialWeight_pos lower length positive mode radius
  have rootSq := annularPotentialWeight_sq lower length positive mode.val.1 mode.val.2 radius inside.1
  have dominated := annularPhaseSlope_dominated parameters length radius mode.val.1 mode.val.2 lengthPositive
    (positive.trans_le inside.1) inside.2 mode.property widthHalf widthLength
  change |annularPhaseSlope parameters mode.val.2 radius /
    annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius| ≤ _
  rw [abs_div, abs_of_pos rootPositive]
  apply (div_le_iff₀ rootPositive).2
  nlinarith [sq_abs (annularPhaseSlope parameters mode.val.2 radius),
    abs_nonneg (annularPhaseSlope parameters mode.val.2 radius)]

def annularPhaseMassMap (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)) (mode : HighAnnularMode) :
    RadialL2 1 lower →L[ℂ] RadialL2 1 lower :=
  scalarRadialMap lower (annularPhaseMassRatio parameters lower length positive mode) (1 / 2)
    (annularPhaseMassRatio_bound parameters lower length positive lengthPositive widthHalf widthLength mode)

theorem annularPhaseMassMap_bound (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (mode : HighAnnularMode) (field : RadialL2 1 lower) :
    ‖annularPhaseMassMap parameters lower length positive lengthPositive widthHalf widthLength mode field‖ ≤
      (1 / 2 : ℝ) * ‖field‖ := scalarRadialMap_bound _ _ _ _ field

end Grad.AnnularVariational
