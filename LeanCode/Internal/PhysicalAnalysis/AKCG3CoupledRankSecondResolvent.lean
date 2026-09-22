import AKCG2CoupledRankLocalization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 200000
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.TensorBootstrap Grad.GenericCarriers

attribute [local irreducible] Grad.PDEBootstrap.firstOrderGraph

private theorem startupFiniteOperatorNorm
    {Input Output Index : Type*}
    [NormedAddCommGroup Input] [NormedSpace ℂ Input]
    [NormedAddCommGroup Output] [NormedSpace ℂ Output]
    (indices : Finset Index) (operators : Index → Input →L[ℂ] Output) :
    ‖∑ index ∈ indices, operators index‖ ≤ ∑ index ∈ indices, ‖operators index‖ := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, ContinuousLinearMap.opNorm_zero, le_refl]
  | @insert index indices missing induction =>
    rw [Finset.sum_insert missing, Finset.sum_insert missing]
    exact (ContinuousLinearMap.opNorm_add_le _ _).trans (add_le_add le_rfl induction)

theorem startupOrderedSecond_compatible (rank : ℕ) (index : TensorIndex) (fields : StartupOrderedH1 rank) :
    startupOrderedValue rank (hilbertLift (Index := DerivativeIndex rank) (startupSecondH1 index) fields) =
      hilbertLift (Index := DerivativeIndex rank) (startupSecondL2 index) (startupOrderedValue rank fields) := by
  apply PiLp.ext
  intro word
  exact startupSecond_compatible index (fields word)

def startupRankPrincipalCoarse {rank : ℕ} (operators : TensorIndex → StartupRankOperator rank 3 3)
    (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar) :
    StartupOrderedL2 rank →L[ℂ] StartupOrderedL2 rank :=
  startupOrderedSecondSum rank (fun index => (operators index).localizedCoarse scalar smooth compact)

def startupRankPrincipalFine {rank : ℕ} (operators : TensorIndex → StartupRankOperator rank 3 3)
    (restriction : FieldH1 →L[ℂ] StartupFirst 3) (extension : StartupFirst 3 →L[ℂ] FieldH1) :
    StartupOrderedH1 rank →L[ℂ] StartupOrderedH1 rank :=
  ∑ index : TensorIndex, (hilbertLift (Index := DerivativeIndex rank) (startupSecondH1 index)).comp
    ((operators index).localizedFine restriction extension)

theorem startupRankPrincipal_compatible {rank : ℕ} (operators : TensorIndex → StartupRankOperator rank 3 3)
    (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar)
    (restriction : FieldH1 →L[ℂ] StartupFirst 3) (extension : StartupFirst 3 →L[ℂ] FieldH1)
    (restrictionBase : ∀ field, startupFirstValue (restriction field) = startupPlaneRestriction (valueInclusion field))
    (extensionBase : ∀ field, valueInclusion (extension field) = startupPlaneExtension (startupCutoffL2 scalar smooth compact (startupFirstValue field)))
    (fields : StartupOrderedH1 rank) :
    startupOrderedValue rank (startupRankPrincipalFine operators restriction extension fields) =
      startupRankPrincipalCoarse operators scalar smooth compact (startupOrderedValue rank fields) := by
  simp only [startupRankPrincipalFine, startupRankPrincipalCoarse, startupOrderedSecondSum,
    sum_apply, map_sum, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro index _
  rw [startupOrderedSecond_compatible, (operators index).localized_compatible scalar smooth compact restriction extension restrictionBase extensionBase]

theorem startupRankPrincipal_bounds {rank : ℕ} (operators : TensorIndex → StartupRankOperator rank 3 3)
    (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar)
    (restriction : FieldH1 →L[ℂ] StartupFirst 3) (extension : StartupFirst 3 →L[ℂ] FieldH1)
    (restrictionNorm : ‖restriction‖ ≤ 1) (extensionNorm : ‖extension‖ ≤ ‖startupCutoffFirst scalar smooth compact‖)
    (bound : ℝ)
    (coarseBound : ∀ index, ‖(operators index).coarse‖ ≤ bound)
    (fineBound : ∀ index, ‖(operators index).fine‖ ≤ bound) :
    ‖startupRankPrincipalCoarse operators scalar smooth compact‖ ≤
        4 * (‖startupCutoffL2 scalar smooth compact‖ * bound) ∧
    ‖startupRankPrincipalFine operators restriction extension‖ ≤
        4 * (‖startupCutoffFirst scalar smooth compact‖ * bound) := by
  constructor
  · apply startupFourComposedBound
      (fun index => hilbertLift (Index := DerivativeIndex rank) (startupSecondL2 index))
      (fun index => (operators index).localizedCoarse scalar smooth compact)
      (‖startupCutoffL2 scalar smooth compact‖ * bound)
    · intro index
      exact (hilbertLift_opNorm_le (Index := DerivativeIndex rank) (startupSecondL2 index)).trans (startupSecondL2_opNorm index)
    · intro index
      exact ((operators index).localizedCoarse_norm scalar smooth compact).trans
        (mul_le_mul_of_nonneg_left (coarseBound index) (norm_nonneg _))
  · let H := StartupOrderedH1 rank
    let group : NormedAddCommGroup H := inferInstanceAs (NormedAddCommGroup (StartupOrderedH1 rank))
    let space : NormedSpace ℂ H := inferInstanceAs (NormedSpace ℂ (StartupOrderedH1 rank))
    let second : TensorIndex → H →L[ℂ] H := fun index =>
      hilbertLift (Index := DerivativeIndex rank) (startupSecondH1 index)
    let localized : TensorIndex → H →L[ℂ] H := fun index =>
      (operators index).localizedFine restriction extension
    let composed : TensorIndex → H →L[ℂ] H := fun index => (second index).comp (localized index)
    unfold startupRankPrincipalFine
    calc
      _ ≤ ∑ index : TensorIndex,
          ‖(hilbertLift (Index := DerivativeIndex rank) (startupSecondH1 index)).comp
            ((operators index).localizedFine restriction extension)‖ :=
        @startupFiniteOperatorNorm H H TensorIndex group space group space Finset.univ composed
      _ ≤ ∑ _index : TensorIndex, 1 * (‖startupCutoffFirst scalar smooth compact‖ * bound) := by
        apply Finset.sum_le_sum
        intro index _
        have secondBound := (hilbertLift_opNorm_le (Index := DerivativeIndex rank)
          (startupSecondH1 index)).trans (startupSecondH1_opNorm index)
        have rowBound := ((operators index).localizedFine_norm scalar smooth compact
          restriction extension restrictionNorm extensionNorm).trans
            (mul_le_mul_of_nonneg_left (fineBound index)
              (norm_nonneg (startupCutoffFirst scalar smooth compact)))
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul secondBound rowBound (ContinuousLinearMap.opNorm_nonneg
            ((operators index).localizedFine restriction extension)) zero_le_one)
      _ = _ := by simp [TensorIndex]


end Grad.CartesianStartup
