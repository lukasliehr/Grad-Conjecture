import AKDN59SameNativeEulerIntegral
import AKM9OriginalWeakLimitCoordinatesAndBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ActualPuncturedFamily
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum Grad.AnnularStrongOrbit
open Grad.AnnularForwardTraces Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularRestriction
open Grad.AnnularExhaustionEstimate Grad.AnnularWeakExhaustion Grad.AnnularFullSource
open Grad.AnnularHighGenerators Grad.AnnularCrossOrbit Grad.ActualAnnularExhaustion
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.SourceCollarFullSource Grad.ExhaustionSourceAllocation
open Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule
  sourceRadialRealInner sourceGraphRealInner sourceKnownGraphRealInner
  weakRetainedRealInner weakSourcesRealInner weakFiveRealInner

attribute [local instance] weakWeightedRetainedRealInner
attribute [local instance] Grad.AnnularStrongOrbit.knownAmbientNormed Grad.AnnularStrongOrbit.knownAmbientSeminormed Grad.AnnularStrongOrbit.knownAmbientRealNormed Grad.AnnularStrongOrbit.knownAmbientRealModule
  Grad.AnnularStrongOrbit.strongCarrierNormed Grad.AnnularStrongOrbit.strongCarrierSeminormed Grad.AnnularStrongOrbit.strongCarrierRealNormed Grad.AnnularStrongOrbit.strongCarrierRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace
  Grad.AnnularCrossOrbit.coupledNormed Grad.AnnularCrossOrbit.coupledSeminormed
  Grad.AnnularCrossOrbit.coupledComplexNormed Grad.AnnularCrossOrbit.coupledComplexModule
  Grad.AnnularCrossOrbit.coupledRealNormed Grad.AnnularCrossOrbit.coupledRealModule
  Grad.AnnularCrossOrbit.coupledOperatorRealNormed Grad.AnnularCrossOrbit.coupledOperatorRealModule




open Grad.FinitePhysicalJetLift Grad.ActualSmoothPhysicalField Grad.ActualNativeCellMoments
open Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.ClosedJets Grad.SourceBoundaryTrace
open MeasureTheory
open scoped ENNReal BigOperators
attribute [local irreducible] originalWeightedDatum

open Grad.NonlinearProduct

/-- Monotonicity of the actual four-source Hilbert norm, at the original width. -/
theorem originalSourceGrade_mono (parameters : PhaseParameters) (source : SmoothQuotient parameters)
    {lower upper : ℕ} (included : lower≤upper) :
    ‖quotientEta parameters lower source‖ ≤ ‖quotientEta parameters upper source‖ := by
  change quotientNorm parameters lower source ≤ quotientNorm parameters upper source
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change quotientNorm parameters lower source^2 ≤ quotientNorm parameters upper source^2
  rw [quotientNorm_sq,quotientNorm_sq]
  exact Finset.sum_le_sum (fun coordinate _ =>
    pow_le_pow_left₀ (originalGradeNorm_nonnegative _ _) (Grad.NonlinearQuotientBounds.originalGradeNorm_mono included (source coordinate)) 2)

/-- The two independent native norm payments give one high source term
and one high coefficient times the independent F9 base. -/
theorem nativeJointPayment_bound (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact) (source : SmoothQuotient parameters)
    (total : ℕ) (cost : ℕ → ℝ) (cost0 : ∀ rank,0≤cost rank)
    (native : ℕ → ℝ)
    (nativeBound : ∀ rank, native rank ≤ cost rank*(‖quotientEta parameters (rank+8) source‖+
      physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (rank+14)*‖quotientEta parameters 8 source‖))
    (low : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 15 ≤ 1) :
    native (total+1)+(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+total))*native 1+
      (‖quotientEta parameters (4+total) source‖+
        (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+total))*‖quotientEta parameters 4 source‖) ≤
    (cost (total+1)+2*cost 1+1)*(‖quotientEta parameters (total+9) source‖+
      (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (total+15))*‖quotientEta parameters 9 source‖) := by
  let budget := fun rank => physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon rank
  let F := fun rank => ‖quotientEta parameters rank source‖
  have F0 (rank : ℕ) : 0≤F rank := norm_nonneg _
  have budget0 (rank : ℕ) : 0≤budget rank := physicalBudget_nonnegative _ _ _ _ _
  have mono {a b : ℕ} (ab : a≤b) : F a≤F b := originalSourceGrade_mono parameters source ab
  have budgetMono {a b : ℕ} (ab : a≤b) : budget a≤budget b := physicalBudget_monotone _ _ _ _ ab
  have eight : F 8≤F 9 := mono (by omega)
  have high := nativeBound (total+1)
  change native (total+1) ≤ cost (total+1)*(F (total+1+8)+budget (total+1+14)*F 8) at high
  rw [show total+1+8=total+9 by omega,show total+1+14=total+15 by omega] at high
  have highPaid : native (total+1)≤cost (total+1)*(F (total+9)+(1+budget (total+15))*F 9) :=
    high.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl _)
      (mul_le_mul (le_add_of_nonneg_left zero_le_one) eight (F0 _) (add_nonneg zero_le_one (budget0 _)))) (cost0 _))
  have base := nativeBound 1
  change native 1≤cost 1*(F 9+budget 15*F 8) at base
  have basePaid : native 1≤2*cost 1*F 9 := by
    have increased := mul_le_mul low eight (F0 _) zero_le_one
    have bound := base.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) increased) (cost0 1))
    nlinarith only [bound]
  have outer : 1+budget (10+total) ≤ 1+budget (total+15) := add_le_add (le_refl _) (budgetMono (by omega))
  have outer0 : 0≤1+budget (10+total) := add_nonneg zero_le_one (budget0 _)
  have baseWeighted := mul_le_mul_of_nonneg_left basePaid outer0
  have baseIncreased := mul_le_mul_of_nonneg_right outer (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) (cost0 1)) (F0 9))
  have sourcePaid : F (4+total)+(1+budget (10+total))*F 4 ≤
      F (total+9)+(1+budget (total+15))*F 9 :=
    add_le_add (mono (by omega)) (mul_le_mul outer (mono (by omega)) (F0 _) (add_nonneg zero_le_one (budget0 _)))
  have missingHigh := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) (cost0 1)) (F0 (total+9))
  change native (total+1)+(1+budget (10+total))*native 1+(F (4+total)+(1+budget (10+total))*F 4)≤_
  nlinarith only [highPaid,baseWeighted,baseIncreased,sourcePaid,missingHigh]

end Grad.OriginalCartesianTameEstimate
