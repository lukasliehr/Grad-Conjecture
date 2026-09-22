import AKCC91RestrictionMinimalProbe
import AKCC92MinimalCutoffExtension
import AKBW20OriginalB10AllRankTensor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 200000
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.TensorBootstrap Grad.GenericCarriers

private theorem startupHilbertLocalization_compatible
    {Index A B C D : Type*} [Fintype Index]
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C]
    [NormedAddCommGroup D] [NormedSpace ℂ D]
    (value : A → B) (baseMap : C → D)
    (restriction : A →L[ℂ] C) (extension : C →L[ℂ] A)
    (roughRestriction : B →L[ℂ] D) (roughExtension : D →L[ℂ] B)
    (cutoff : D →L[ℂ] D)
    (fine : PiLp 2 (fun _ : Index => C) →L[ℂ] PiLp 2 (fun _ : Index => C))
    (coarse : PiLp 2 (fun _ : Index => D) →L[ℂ] PiLp 2 (fun _ : Index => D))
    (restrictSame : ∀ field, baseMap (restriction field) = roughRestriction (value field))
    (extendSame : ∀ field, value (extension field) = roughExtension (cutoff (baseMap field)))
    (compatible : ∀ fields, WithLp.toLp 2 (fun index => baseMap (fine fields index)) =
      coarse (WithLp.toLp 2 (fun index => baseMap (fields index))))
    (fields : PiLp 2 (fun _ : Index => A)) :
    WithLp.toLp 2 (fun index => value
      (hilbertLift (Index := Index) extension
        (fine (hilbertLift (Index := Index) restriction fields)) index)) =
      hilbertLift (Index := Index) roughExtension
        (hilbertLift (Index := Index) cutoff
          (coarse (hilbertLift (Index := Index) roughRestriction
            (WithLp.toLp 2 (fun index => value (fields index)))))) := by
  have restrictions : WithLp.toLp 2 (fun index => baseMap
      (hilbertLift (Index := Index) restriction fields index)) =
      hilbertLift (Index := Index) roughRestriction
        (WithLp.toLp 2 (fun index => value (fields index))) := by
    apply PiLp.ext
    intro index
    exact restrictSame (fields index)
  have identity := compatible (hilbertLift (Index := Index) restriction fields)
  rw [restrictions] at identity
  apply PiLp.ext
  intro index
  change value (extension (fine (hilbertLift (Index := Index) restriction fields) index)) = _
  rw [extendSame]
  exact congrArg (fun tuple : PiLp 2 (fun _ : Index => D) => roughExtension (cutoff (tuple index))) identity

namespace StartupRankOperator

def orderedCoarse {rank : ℕ} (operator : StartupRankOperator rank 3 3) :
    Tensor rank (StartupL2 3) →L[ℂ] Tensor rank (StartupL2 3) :=
  (startupTensorFieldEquiv 3 rank).symm.toLinearIsometry.toContinuousLinearMap.comp
    (operator.coarse.comp (startupTensorFieldEquiv 3 rank).toLinearIsometry.toContinuousLinearMap)

def orderedFine {rank : ℕ} (operator : StartupRankOperator rank 3 3) :
    StartupTensorFirst 3 rank →L[ℂ] StartupTensorFirst 3 rank :=
  (startupTensorFirstEquiv 3 rank).symm.toLinearIsometry.toContinuousLinearMap.comp
    (operator.fine.comp (startupTensorFirstEquiv 3 rank).toLinearIsometry.toContinuousLinearMap)

theorem orderedCoarse_norm {rank : ℕ} (operator : StartupRankOperator rank 3 3) :
    ‖operator.orderedCoarse‖ ≤ ‖operator.coarse‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg operator.coarse)
  intro fields
  change ‖(startupTensorFieldEquiv 3 rank).symm (operator.coarse (startupTensorFieldEquiv 3 rank fields))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (operator.coarse.le_opNorm _).trans_eq (by rw [LinearIsometryEquiv.norm_map])

theorem orderedFine_norm {rank : ℕ} (operator : StartupRankOperator rank 3 3) :
    ‖operator.orderedFine‖ ≤ ‖operator.fine‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg operator.fine)
  intro fields
  change ‖(startupTensorFirstEquiv 3 rank).symm (operator.fine (startupTensorFirstEquiv 3 rank fields))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (operator.fine.le_opNorm _).trans_eq (by rw [LinearIsometryEquiv.norm_map])

theorem ordered_compatible {rank : ℕ} (operator : StartupRankOperator rank 3 3) (fields : StartupTensorFirst 3 rank) :
    startupTensorFirstValues (operator.orderedFine fields) = operator.orderedCoarse (startupTensorFirstValues fields) := by
  change startupTensorFirstValues ((startupTensorFirstEquiv 3 rank).symm (operator.fine (startupTensorFirstEquiv 3 rank fields))) = _
  rw [startupTensorFirstEquiv_symm_values]
  change (startupTensorFieldEquiv 3 rank).symm
    (Grad.WeightedJets.base (startupTensorDimension 3 rank) 1 openUnitDisk (fun _ => 0)
      (operator.fine (startupTensorFirstEquiv 3 rank fields))) = _
  rw [operator.compatible]
  rw [show Grad.WeightedJets.base (startupTensorDimension 3 rank) 1 openUnitDisk (fun _ => 0)
      (startupTensorFirstEquiv 3 rank fields) = _ from startupTensorFirstEquiv_base 3 rank fields]
  rfl

def localizedCoarse {rank : ℕ} (operator : StartupRankOperator rank 3 3)
    (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar) :
    StartupOrderedL2 rank →L[ℂ] StartupOrderedL2 rank :=
  (hilbertLift (Index := DerivativeIndex rank) startupPlaneExtension).comp
    ((hilbertLift (Index := DerivativeIndex rank) (startupCutoffL2 scalar smooth compact)).comp
      (operator.orderedCoarse.comp (hilbertLift (Index := DerivativeIndex rank) startupPlaneRestriction)))

def localizedFine {rank : ℕ} (operator : StartupRankOperator rank 3 3)
    (restriction : FieldH1 →L[ℂ] StartupFirst 3) (extension : StartupFirst 3 →L[ℂ] FieldH1) :
    StartupOrderedH1 rank →L[ℂ] StartupOrderedH1 rank :=
  (hilbertLift (Index := DerivativeIndex rank) extension).comp
    (operator.orderedFine.comp (hilbertLift (Index := DerivativeIndex rank) restriction))

theorem localized_compatible {rank : ℕ} (operator : StartupRankOperator rank 3 3)
    (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar)
    (restriction : FieldH1 →L[ℂ] StartupFirst 3) (extension : StartupFirst 3 →L[ℂ] FieldH1)
    (restrictionBase : ∀ field, startupFirstValue (restriction field) = startupPlaneRestriction (valueInclusion field))
    (extensionBase : ∀ field, valueInclusion (extension field) = startupPlaneExtension (startupCutoffL2 scalar smooth compact (startupFirstValue field)))
    (fields : StartupOrderedH1 rank) :
    startupOrderedValue rank (operator.localizedFine restriction extension fields) =
      operator.localizedCoarse scalar smooth compact (startupOrderedValue rank fields) := by
  exact startupHilbertLocalization_compatible
    (Index := DerivativeIndex rank) valueInclusion startupFirstValue
    restriction extension startupPlaneRestriction startupPlaneExtension
    (startupCutoffL2 scalar smooth compact) operator.orderedFine operator.orderedCoarse
    restrictionBase extensionBase operator.ordered_compatible fields

theorem localizedCoarse_norm {rank : ℕ} (operator : StartupRankOperator rank 3 3)
    (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar) :
    ‖operator.localizedCoarse scalar smooth compact‖ ≤ ‖startupCutoffL2 scalar smooth compact‖ * ‖operator.coarse‖ := by
  have extension := (hilbertLift_opNorm_le (Index := DerivativeIndex rank) startupPlaneExtension).trans startupPlaneExtension_opNorm
  have restriction := (hilbertLift_opNorm_le (Index := DerivativeIndex rank) startupPlaneRestriction).trans startupPlaneRestriction_opNorm
  have bounded := startupComposition_norm _ _ extension
    (startupComposition_norm _ _ (hilbertLift_opNorm_le (Index := DerivativeIndex rank) (startupCutoffL2 scalar smooth compact))
      (startupComposition_norm _ _ operator.orderedCoarse_norm restriction))
  simpa only [localizedCoarse, one_mul, mul_one] using bounded

theorem localizedFine_norm {rank : ℕ} (operator : StartupRankOperator rank 3 3)
    (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar)
    (restriction : FieldH1 →L[ℂ] StartupFirst 3) (extension : StartupFirst 3 →L[ℂ] FieldH1)
    (restrictionNorm : ‖restriction‖ ≤ 1) (extensionNorm : ‖extension‖ ≤ ‖startupCutoffFirst scalar smooth compact‖) :
    ‖operator.localizedFine restriction extension‖ ≤ ‖startupCutoffFirst scalar smooth compact‖ * ‖operator.fine‖ := by
  have extendBound := (hilbertLift_opNorm_le (Index := DerivativeIndex rank) extension).trans extensionNorm
  have restrictBound := (hilbertLift_opNorm_le (Index := DerivativeIndex rank) restriction).trans restrictionNorm
  have bounded := startupComposition_norm _ _ extendBound (startupComposition_norm _ _ operator.orderedFine_norm restrictBound)
  simpa only [localizedFine, mul_one] using bounded

end StartupRankOperator
end Grad.CartesianStartup
