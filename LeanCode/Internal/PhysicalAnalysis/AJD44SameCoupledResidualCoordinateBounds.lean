import AJD43SameOffDiagonalCoordinateBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.AnnularKernelOrbit Grad.AnnularCoupledInverse

section Assembly
variable {Context : Type*} {H E : Context → Type*}
  [∀ context, NormedAddCommGroup (H context)] [∀ context, NormedSpace ℂ (H context)]
  [∀ context, NormedAddCommGroup (E context)] [∀ context, NormedSpace ℂ (E context)]
  {budget : Context → ℕ → ℝ}

private theorem leftProjection_norm (context : Context) :
    ‖(ContinuousLinearMap.fst ℂ (H context) (E context)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ (H context) (E context)).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro value
  have square := WithLp.prod_norm_sq_eq_of_L2 value
  change ‖value‖ ^ 2 = ‖value.ofLp.1‖ ^ 2 + ‖value.ofLp.2‖ ^ 2 at square
  change ‖value.ofLp.1‖ ≤ 1 * ‖value‖
  nlinarith [norm_nonneg value, norm_nonneg value.ofLp.1, sq_nonneg ‖value.ofLp.2‖]

private theorem rightProjection_norm (context : Context) :
    ‖(ContinuousLinearMap.snd ℂ (H context) (E context)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ (H context) (E context)).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro value
  have square := WithLp.prod_norm_sq_eq_of_L2 value
  change ‖value‖ ^ 2 = ‖value.ofLp.1‖ ^ 2 + ‖value.ofLp.2‖ ^ 2 at square
  change ‖value.ofLp.2‖ ≤ 1 * ‖value‖
  nlinarith [norm_nonneg value, norm_nonneg value.ofLp.2, sq_nonneg ‖value.ofLp.1‖]

theorem UniformCoordinateBound.offDiagonal
    {upper : (context : Context) → OrbitParameter → E context →L[ℂ] H context}
    {lower : (context : Context) → OrbitParameter → H context →L[ℂ] E context}
    (upperBound : UniformCoordinateBound budget upper) (lowerBound : UniformCoordinateBound budget lower)
    (upperSmooth : ∀ context, ContDiff ℝ ∞ (upper context))
    (lowerSmooth : ∀ context, ContDiff ℝ ∞ (lower context)) :
    UniformCoordinateBound budget (fun context tau => hilbertOffDiagonal (upper context tau) (lower context tau)) := by
  have high := upperBound.precomposeComplex upperSmooth
    (fun context => (ContinuousLinearMap.snd ℂ (H context) (E context)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ (H context) (E context)).toContinuousLinearMap)
    1 (by norm_num) rightProjection_norm
  have low := lowerBound.precomposeComplex lowerSmooth
    (fun context => (ContinuousLinearMap.fst ℂ (H context) (E context)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ (H context) (E context)).toContinuousLinearMap)
    1 (by norm_num) leftProjection_norm
  exact high.pairComplex low
    (fun context => complexOperatorComposition_contDiff _ _ (upperSmooth context) contDiff_const)
    (fun context => complexOperatorComposition_contDiff _ _ (lowerSmooth context) contDiff_const)
end Assembly

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularCrossMaps
open Grad.AnnularCoupledOrbit

attribute [local instance] crossDataNormed crossDataSeminormed crossDataRealInner crossDataRealNormed crossDataRealModule
  crossHighNormed crossHighSeminormed crossHighComplexNormed crossHighComplexModule crossHighRealNormed crossHighRealModule
  coupledNormed coupledSeminormed coupledComplexNormed coupledComplexModule
  coupledRealNormed coupledRealModule coupledOperatorRealNormed coupledOperatorRealModule

local instance coupledCoordinateOperatorNormed (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    NormedAddCommGroup (CoupledSpace lower L positive lengthPositive →L[ℂ] CoupledSpace lower L positive lengthPositive) := inferInstance

variable (parameters : PhaseParameters) (L compact : ℝ) (lengthPositive : 0 < L)
include lengthPositive

theorem coupledOrbitError_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        coupledOrbitError parameters context.lower L compact context.lengthPositive context.positive context.lowerHalf
          context.widthHalf context.widthLength context.state context.small) := by
  have assembled := UniformCoordinateBound.offDiagonal
    (budget := CoupledCoordinateContext.budget)
    (H := fun context : CoupledCoordinateContext parameters L compact => CrossHighSpace context.lower L context.positive context.lengthPositive)
    (E := fun context : CoupledCoordinateContext parameters L compact => lowEnergyGraph context.lower L context.positive)
    (upper := fun context => actualHighOffDiagonalOrbit parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf
      context.widthHalf context.widthLength context.state context.small)
    (lower := fun context => actualLowOffDiagonalOrbit parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf context.state)
    (by
      intro axis order
      let constant : ℝ := (actualHighOffDiagonalOrbit_uniformCoordinateBound parameters L compact axis order).choose
      refine ⟨constant, (actualHighOffDiagonalOrbit_uniformCoordinateBound parameters L compact axis order).choose_spec.1, ?_⟩
      intro context base time
      with_unfolding_all
        exact (actualHighOffDiagonalOrbit_uniformCoordinateBound parameters L compact axis order).choose_spec.2 context base time)
    (by
      intro axis order
      let constant : ℝ := (actualLowOffDiagonalOrbit_uniformCoordinateBound parameters L compact lengthPositive axis order).choose
      refine ⟨constant, (actualLowOffDiagonalOrbit_uniformCoordinateBound parameters L compact lengthPositive axis order).choose_spec.1, ?_⟩
      intro context base time
      with_unfolding_all
        exact (actualLowOffDiagonalOrbit_uniformCoordinateBound parameters L compact lengthPositive axis order).choose_spec.2 context base time)
    (fun context => actualHighOffDiagonalOrbit_contDiff parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf
      context.widthHalf context.widthLength context.state context.small)
    (fun context => actualLowOffDiagonalOrbit_contDiff parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf context.state context.small)
  intro axis order
  obtain ⟨constant, nonnegative, estimate⟩ := assembled axis order
  refine ⟨constant, nonnegative, ?_⟩
  intro context base time
  have converted := estimate context base time
  simp only [← coupledOrbitError_assembly] at converted
  with_unfolding_all exact converted

theorem coupledResidualOrbit_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        coupledResidualOrbit parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf
          context.widthHalf context.widthLength context.state context.small) := by
  have identity := UniformCoordinateBound.const (budget := CoupledCoordinateContext.budget)
    (fun context : CoupledCoordinateContext parameters L compact => context.budget_nonnegative)
    (fun context => ContinuousLinearMap.id ℂ (CoupledSpace context.lower L context.positive context.lengthPositive))
    1 (by norm_num) (fun _ => ContinuousLinearMap.norm_id_le)
  have errorSmooth (context : CoupledCoordinateContext parameters L compact) :=
    coupledOrbitError_contDiff parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf
      context.widthHalf context.widthLength context.state context.small
  have combined := identity.add ((coupledOrbitError_uniformCoordinateBound parameters L compact lengthPositive).neg errorSmooth)
    (fun _ => contDiff_const) (fun context => (errorSmooth context).neg)
  intro axis order
  obtain ⟨constant, nonnegative, estimate⟩ := combined axis order
  refine ⟨constant, nonnegative, ?_⟩
  intro context base time
  have converted := estimate context base time
  simp only [← sub_eq_add_neg] at converted
  with_unfolding_all exact converted
end Grad.AnnularCrossOrbit
