import AKDP5ActualLedgerDeviationProfiles
import AKCG8ActualFixedMatrixDerivativeSplit

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

/-- Finite Hilbert tuples can be estimated componentwise without changing
any derivative or cell weight. -/
theorem startupFiniteHilbert_norm_le_sum {Index Value : Type*} [Fintype Index]
    [NormedAddCommGroup Value] (values : Index → Value) :
    ‖(WithLp.toLp 2 values : PiLp 2 (fun _ : Index => Value))‖ ≤ ∑ index,‖values index‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

/-- The whole literal nonempty-allocation tensor has the same one-high
bound as each coordinate; the finite rank multiplicity only changes its
constant, chosen before the coefficient state and the unknown. -/
theorem startupMatrixTensorRemainder_oneHigh (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (offset rank : ℕ) (profile : EstimateProfile)
    (fixedNonnegative : ∀ grade,0≤profile.fixed grade)
    (deviationNonnegative : ∀ grade,0≤profile.deviation grade)
    (epsilon : ℝ) (epsilonPositive : 0<epsilon) :
    ∃ constant : ℝ, 0≤constant ∧
    ∀ (input output order weight : ℕ) (baseField : ACore parameters 3) (rho curvature : ℝ)
      (family reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output)
      (estimate : FamilyEstimate parameters baseField rho curvature offset profile family reference)
      (core : ACore parameters input) (jet : GraphGrade input order weight openUnitDisk)
      (_same : base input order openUnitDisk (fun _ => weight) jet = (originalSourceMoments parameters core).field)
      (bound : rank≤order) (reserve : rank-1≤weight),
      physicalBudget parameters baseField rho curvature offset≤1 →
      ‖(WithLp.toLp 2 (fun word : TensorBootstrap.DerivativeIndex rank =>
        startupMatrixOrderedRemainder admissible family estimate.actualCoherent word bound reserve jet) :
          Tensor rank (StartupL2 output))‖ ≤
        epsilon*originalGradeNorm rank core+
          constant*((1+physicalBudget parameters baseField rho curvature (offset+rank))*originalGradeNorm 0 core) := by
  classical
  let count : ℝ := Fintype.card (TensorBootstrap.DerivativeIndex rank)
  let delta := epsilon/(count+1)
  have countNonnegative : 0≤count := Nat.cast_nonneg _
  have deltaPositive : 0<delta := div_pos epsilonPositive (by linarith)
  have each (word : TensorBootstrap.DerivativeIndex rank) := startupMatrixOrderedRemainder_oneHigh parameters admissible
    offset rank word profile fixedNonnegative deviationNonnegative delta deltaPositive
  choose constants nonnegative estimates using each
  refine ⟨∑ word,constants word,Finset.sum_nonneg (fun word _ => nonnegative word),?_⟩
  intro input output order weight baseField rho curvature family reference estimate core jet same bound reserve low
  apply (startupFiniteHilbert_norm_le_sum _).trans
  apply (Finset.sum_le_sum (fun word _ => estimates word input output order weight baseField rho curvature
    family reference estimate core jet same bound reserve low)).trans
  rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.sum_mul]
  have leading : count*delta≤epsilon := by
    have ratio : count/(count+1)≤1 := (div_le_one (by linarith)).mpr (by linarith)
    calc
      _ = epsilon*(count/(count+1)) := by dsimp only [delta]; ring
      _ ≤ epsilon*1 := mul_le_mul_of_nonneg_left ratio epsilonPositive.le
      _ = _ := mul_one _
  exact add_le_add (by
    change count*(delta*originalGradeNorm rank core)≤_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right leading (originalGradeNorm_nonnegative rank core)) le_rfl

end Grad.CartesianStartup
