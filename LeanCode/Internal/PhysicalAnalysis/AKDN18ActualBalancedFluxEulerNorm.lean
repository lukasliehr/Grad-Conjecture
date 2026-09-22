import AKDN17ActualPhaseCurveEulerNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothness Grad.AnnularWeightedSystem Grad.BoundaryLift

def balancedFluxSlope (parameters : PhaseParameters) (length : ℝ) : PhysicalHilbertTriple →L[ℂ] PhysicalHilbertPair :=
  balancedFluxOutput parameters length 1-balancedFluxOutput parameters length 0

theorem balancedFluxOutput_affine (parameters : PhaseParameters) (length radius : ℝ) :
    balancedFluxOutput parameters length radius = balancedFluxOutput parameters length 0+radius • balancedFluxSlope parameters length := by
  apply ContinuousLinearMap.ext
  intro field
  rcases field with ⟨first,second,third⟩
  change balancedFluxOutput parameters length radius (first,(second,third)) =
    balancedFluxOutput parameters length 0 (first,(second,third))+
      radius • (balancedFluxOutput parameters length 1 (first,(second,third))-
        balancedFluxOutput parameters length 0 (first,(second,third)))
  rw [balancedFluxOutput_actual,balancedFluxOutput_actual,balancedFluxOutput_actual]
  apply Prod.ext
  · change hilbertMeanFree parameters first = hilbertMeanFree parameters first+
      radius • (hilbertMeanFree parameters first-hilbertMeanFree parameters first)
    rw [sub_self,smul_zero,add_zero]
  · apply lp.ext
    funext mode
    change -((radius : ℂ)*(length : ℂ)⁻¹) • (hilbertFrequencyOperator parameters 1 (some true) second mode)-
        hilbertFrequencyOperator parameters 1 (some false) third mode =
      (-((0 : ℂ)*(length : ℂ)⁻¹) • (hilbertFrequencyOperator parameters 1 (some true) second mode)-
        hilbertFrequencyOperator parameters 1 (some false) third mode)+
      radius • ((-((1 : ℂ)*(length : ℂ)⁻¹) • (hilbertFrequencyOperator parameters 1 (some true) second mode)-
        hilbertFrequencyOperator parameters 1 (some false) third mode)-
       (-((0 : ℂ)*(length : ℂ)⁻¹) • (hilbertFrequencyOperator parameters 1 (some true) second mode)-
        hilbertFrequencyOperator parameters 1 (some false) third mode))
    apply PiLp.ext
    intro coordinate
    simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,←Complex.coe_smul,smul_eq_mul]
    ring

def balancedFluxEuler (parameters : PhaseParameters) (length : ℝ) : ℕ → ℝ → (PhysicalHilbertTriple →L[ℂ] PhysicalHilbertPair) :=
  affineEulerJets (balancedFluxOutput parameters length 0) (balancedFluxSlope parameters length)

theorem balancedFluxEuler_fidelity (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (rank : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    vectorEulerWithinIteratedDerivative (Icc lower 1) rank (balancedFluxOutput parameters length) radius =
      balancedFluxEuler parameters length rank radius := by
  rw [show balancedFluxOutput parameters length = fun point => balancedFluxOutput parameters length 0+point • balancedFluxSlope parameters length from
    funext (balancedFluxOutput_affine parameters length)]
  exact affineEulerJets_fidelity _ _ (Icc lower 1) (uniqueDiffOn_Icc bounded)
    (fun point member => (positive.trans_le member.1).ne') rank radius inside

def balancedFluxApply :
    (PhysicalHilbertTriple →L[ℂ] PhysicalHilbertPair) →L[ℝ] PhysicalHilbertTriple →L[ℝ] PhysicalHilbertPair :=
  ((ContinuousLinearMap.apply ℝ PhysicalHilbertPair).flip).comp
    (ContinuousLinearMap.restrictScalarsIsometry ℂ PhysicalHilbertTriple PhysicalHilbertPair ℝ ℝ).toContinuousLinearMap

theorem balancedFluxCurve_EulerBound (parameters : PhaseParameters) (length : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (lower : ℝ) (_positive : 0 < lower) (_bounded : lower < 1)
      (curve : ℝ → PhysicalHilbertTriple) (rank : ℕ),
    ContDiffOn ℝ rank curve (Icc lower 1) →
    ∀ radius : RadialPoint, radius.val ∈ Icc lower 1 →
    ‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (fun point => balancedFluxOutput parameters length point (curve point)) radius.val‖ ≤
      constant*eulerAllocationSum
        (fun _ inputRank => ‖vectorEulerWithinIteratedDerivative (Icc lower 1) inputRank curve radius.val‖)
        (eulerLeibnizTerms rank) := by
  let constant := ‖balancedFluxOutput parameters length 0‖+‖balancedFluxSlope parameters length‖
  have bound (rank : ℕ) (radius : RadialPoint) : ‖balancedFluxEuler parameters length rank radius‖ ≤ constant :=
    affineEulerJets_bound _ _ rank radius
  refine ⟨constant,add_nonneg (norm_nonneg _) (norm_nonneg _),?_⟩
  intro lower positive bounded curve rank curveSmooth radius inside
  have smooth : ContDiff ℝ ∞ (balancedFluxOutput parameters length) := by
    rw [show balancedFluxOutput parameters length = fun point => balancedFluxOutput parameters length 0+point • balancedFluxSlope parameters length from
      funext (balancedFluxOutput_affine parameters length)]
    exact contDiff_const.add (contDiff_id.smul contDiff_const)
  have operatorSmooth : ContDiffOn ℝ rank (balancedFluxOutput parameters length) (Icc lower 1) :=
    contDiffOn_infty.mp smooth.contDiffOn rank
  have actual := vectorEulerWithin_bilinear balancedFluxApply (Icc lower 1) (uniqueDiffOn_Icc bounded)
    (fun point member => (positive.trans_le member.1).ne') (balancedFluxOutput parameters length) curve rank operatorSmooth curveSmooth inside
  change vectorEulerWithinIteratedDerivative (Icc lower 1) rank
    (fun point => balancedFluxOutput parameters length point (curve point)) radius.val = _ at actual
  rw [actual,eulerAllocationSum_mul_left]
  apply (bilinearEulerPolynomial_norm balancedFluxApply _ _ _ radius.val).trans
  apply eulerAllocationSum_mono
  intro term _
  change ‖vectorEulerWithinIteratedDerivative (Icc lower 1) term.1 (balancedFluxOutput parameters length) radius.val
    (vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 curve radius.val)‖ ≤ _
  rw [balancedFluxEuler_fidelity parameters length lower positive bounded term.1 radius.val inside]
  exact ((balancedFluxEuler parameters length term.1 radius).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (bound term.1 radius) (norm_nonneg _))

end Grad.OriginalCartesianTameEstimate
