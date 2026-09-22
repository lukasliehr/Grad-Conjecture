import AKDP6ActualMatrixTensorOneHigh

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.ActualOriginalSourceMoments Grad.WeightedJets.Ordered Grad.NonlinearProduct Grad.TensorBootstrap
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.OriginalCartesianTameEstimate Grad.RepresentedKernel.SpatialProduct

/-- The literal CG8 fixed angular/reflection action on the actual
coefficient remainder retains a single adjustable high input. Its fixed
operator norm is independent of rank. -/
theorem startupFixedMatrixTensorRemainder_oneHigh
    {Parameter : Type*} [MeasurableSpace Parameter] (measure : Measure Parameter) [SigmaFinite measure]
    (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (offset rank middle output : ℕ) (profile : EstimateProfile)
    (fixedNonnegative : ∀ grade,0≤profile.fixed grade)
    (deviationNonnegative : ∀ grade,0≤profile.deviation grade)
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue middle output)
    (integrable : Integrable coefficient measure)
    (liftMeasurable : Measurable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)))
    (liftIntegrable : Integrable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)) measure)
    (epsilon : ℝ) (epsilonPositive : 0<epsilon) :
    ∃ constant : ℝ,0≤constant ∧
    ∀ (input order weight : ℕ) (baseField : ACore parameters 3) (rho curvature : ℝ)
      (family reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell input middle)
      (estimate : FamilyEstimate parameters baseField rho curvature offset profile family reference)
      (core : ACore parameters input) (jet : GraphGrade input order weight openUnitDisk)
      (_same : base input order openUnitDisk (fun _ => weight) jet = (originalSourceMoments parameters core).field)
      (bound : rank≤order) (reserve : rank-1≤weight),
      physicalBudget parameters baseField rho curvature offset≤1 →
      ‖startupFixedTensorKernel measure rank orthogonal invariant actionMeasurable coefficient liftMeasurable liftIntegrable
        (WithLp.toLp 2 (fun word : TensorBootstrap.DerivativeIndex rank =>
          startupMatrixOrderedRemainder admissible family estimate.actualCoherent word bound reserve jet))‖ ≤
        epsilon*originalGradeNorm rank core+
          constant*((1+physicalBudget parameters baseField rho curvature (offset+rank))*originalGradeNorm 0 core) := by
  let fixedBound := ∫ parameter,‖coefficient parameter‖ ∂measure
  have operatorNonnegative : 0≤fixedBound := integral_nonneg (fun _ => norm_nonneg _)
  let delta := epsilon/(fixedBound+1)
  have deltaPositive : 0<delta := div_pos epsilonPositive (by linarith)
  obtain ⟨constant,nonnegative,estimate⟩ := startupMatrixTensorRemainder_oneHigh parameters admissible offset rank profile
    fixedNonnegative deviationNonnegative delta deltaPositive
  refine ⟨fixedBound*constant,mul_nonneg operatorNonnegative nonnegative,?_⟩
  intro input order weight baseField rho curvature family reference actual core jet same bound reserve low
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  apply (mul_le_mul (startupFixedTensorKernel_norm measure rank orthogonal invariant actionMeasurable coefficient
    liftMeasurable liftIntegrable integrable)
    (estimate input middle order weight baseField rho curvature family reference actual core jet same bound reserve low)
    (norm_nonneg _) operatorNonnegative).trans
  have leading : fixedBound*delta≤epsilon := by
    have ratio : fixedBound/(fixedBound+1)≤1 := (div_le_one (by linarith)).mpr (by linarith)
    calc
      _ = epsilon*(fixedBound/(fixedBound+1)) := by dsimp only [delta]; ring
      _ ≤ epsilon*1 := mul_le_mul_of_nonneg_left ratio epsilonPositive.le
      _ = _ := mul_one _
  calc
    _ = (fixedBound*delta)*originalGradeNorm rank core+(fixedBound*constant)*
      ((1+physicalBudget parameters baseField rho curvature (offset+rank))*originalGradeNorm 0 core) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right leading (originalGradeNorm_nonnegative rank core)) le_rfl

end Grad.CartesianStartup
