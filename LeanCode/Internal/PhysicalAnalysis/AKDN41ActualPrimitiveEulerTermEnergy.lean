import AKDN40ActualWeightedKappaPrimitive
import AKDK12OriginalScalarTerminalEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.AnnularGeneralSourceRegularity
open Grad.FlatSourceProjection Grad.QuotientProjection Grad.AnnularWeightedSmoothness Grad.AnnularSmoothCore
open Grad.AnnularKernelL2 Grad.GaugeCoefficients.Physical.Allocation Grad.OriginalTerminalAllocation

theorem actualPrimitiveEuler_continuous (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (source : SmoothQuotient parameters)
    (slot : Fin 4) (power rank : ℕ) :
    ContinuousOn (vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (actualCartesianPrimitiveCurve parameters length lower positive bounded source slot power)) (Icc lower 1) := by
  unfold actualCartesianPrimitiveCurve
  exact (vectorEulerWithin_smooth (Icc lower 1) (uniqueDiffOn_Icc bounded)
    ((actualCartesianPrimitiveRadialCurves parameters length lower positive bounded source slot).curve power) rank 0
    (by simpa only [Nat.zero_add] using (contDiffOn_infty.mp
      ((actualCartesianPrimitiveRadialCurves parameters length lower positive bounded source slot).smooth power) rank))).continuousOn

/-- Every complementary terminal from the actual kappa product has a
uniform SAME-source F_(q+4)/F4 energy payment, with the original total rank. -/
theorem actualPrimitiveEulerTerm_pairEnergy (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (total extra power rank : ℕ)
    (paid : extra+power+rank ≤ total) (slot : Fin 4) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (field : ACore parameters 3) (rho epsilon : ℝ), physicalBudget parameters field rho epsilon 10 ≤ 1 →
    ∀ source : SmoothQuotient parameters, ∀ first second : ℕ, first+second=rank →
    let budget := fun order => 1+physicalBudget parameters field rho epsilon (10+order)
    let primitive := actualCartesianPrimitiveCurve parameters length lower positive bounded source slot
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖‖budget (extra+first) • vectorEulerWithinIteratedDerivative (Icc lower 1) second (primitive power) radius‖+
         ‖budget (extra+first+power) • vectorEulerWithinIteratedDerivative (Icc lower 1) second (primitive 0) radius‖‖^2)) ≤
      ENNReal.ofReal ((constant*(‖quotientEta parameters (4+total) source‖+
        (1+physicalBudget parameters field rho epsilon (10+total))*‖quotientEta parameters 4 source‖))^2) := by
  choose highConstant high0 highEnergy using
    (fun first : Fin (rank+1) => actualPrimitive_jointTerminalEnergy parameters length lower positive bounded
      total (extra+first.val) power (rank-first.val) (by omega))
  choose lowConstant low0 lowEnergy using
    (fun first : Fin (rank+1) => actualPrimitive_jointTerminalEnergy parameters length lower positive bounded
      total (extra+first.val+power) 0 (rank-first.val) (by omega))
  obtain ⟨constant,constantOne,uniform⟩ := finiteUniformMajorant
    (fun first : Fin (rank+1) => highConstant first slot+lowConstant first slot)
  have constant0 : 0 ≤ constant := zero_le_one.trans constantOne
  refine ⟨2*constant,mul_nonneg (by norm_num) constant0,?_⟩
  intro field rho epsilon unit source first second allocated
  dsimp only
  let index : Fin (rank+1) := ⟨first,by omega⟩
  let budget := fun order => 1+physicalBudget parameters field rho epsilon (10+order)
  let primitive := actualCartesianPrimitiveCurve parameters length lower positive bounded source slot
  let payment := ‖quotientEta parameters (4+total) source‖+
    (1+physicalBudget parameters field rho epsilon (10+total))*‖quotientEta parameters 4 source‖
  have payment0 : 0 ≤ payment := add_nonneg (norm_nonneg _)
    (mul_nonneg (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)) (norm_nonneg _))
  let high := fun radius => budget (extra+first) • vectorEulerWithinIteratedDerivative (Icc lower 1) second (primitive power) radius
  let low := fun radius => budget (extra+first+power) • vectorEulerWithinIteratedDerivative (Icc lower 1) second (primitive 0) radius
  have highM : AEStronglyMeasurable high (volume.restrict (Icc lower 1)) :=
    ((actualPrimitiveEuler_continuous parameters length lower positive bounded source slot power second).const_smul
      (budget (extra+first))).aestronglyMeasurable measurableSet_Icc
  have lowM : AEStronglyMeasurable low (volume.restrict (Icc lower 1)) :=
    ((actualPrimitiveEuler_continuous parameters length lower positive bounded source slot 0 second).const_smul
      (budget (extra+first+power))).aestronglyMeasurable measurableSet_Icc
  have highPaid : (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖high radius‖^2)) ≤
      ENNReal.ofReal ((highConstant index slot*payment)^2) := by
    have actual := highEnergy index field rho epsilon unit source slot
    simpa only [index,show rank-first=second by omega] using actual
  have lowPaid : (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖low radius‖^2)) ≤
      ENNReal.ofReal ((lowConstant index slot*payment)^2) := by
    have actual := lowEnergy index field rho epsilon unit source slot
    simpa only [index,show rank-first=second by omega] using actual
  have actual := twoInput_squareEnergy (volume.restrict (Icc lower 1))
    (fun radius => ‖high radius‖+‖low radius‖) high low highM lowM 1 1
    (highConstant index slot*payment) (lowConstant index slot*payment)
    zero_le_one zero_le_one (mul_nonneg (high0 index slot) payment0) (mul_nonneg (low0 index slot) payment0)
    (Filter.Eventually.of_forall (fun radius => by
      rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),one_mul,one_mul])) highPaid lowPaid
  apply actual.trans
  apply ENNReal.ofReal_le_ofReal
  have highNonnegative := high0 index slot
  have lowNonnegative := low0 index slot
  apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
  have selected : highConstant index slot+lowConstant index slot ≤ constant :=
    (le_abs_self _).trans (uniform index)
  have final := mul_le_mul_of_nonneg_right selected payment0
  nlinarith only [final]

end Grad.OriginalCartesianTameEstimate
