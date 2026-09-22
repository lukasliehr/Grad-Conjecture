import AKDN70ActualCovariantJointEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.AnnularSmoothCore
open Grad.AnnularReconstruction Grad.AnnularKernelL2

/-- The fixed affine seven-input assembly preserves the joint Euler
energy payment without adding a coefficient factor. -/
theorem balancedInputCurve_squareEnergy (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (rank : ℕ) :
    ∃ constant : ℝ, 0≤constant ∧
    ∀ (curve : ℝ → PhysicalHilbertPair), ContDiffOn ℝ ∞ curve (Icc lower 1) →
    ∀ weight payment : ℝ, 0≤weight → 0≤payment →
    (∀ order≤rank, (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) order curve radius‖^2)) ≤ ENNReal.ofReal (payment^2)) →
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank
        (fun point => balancedSevenInput parameters point (curve point)) radius‖^2)) ≤ ENNReal.ofReal ((constant*payment)^2) := by
  obtain ⟨action,action0,bound⟩ := balancedInputCurve_EulerBound parameters
  refine ⟨action*(4:ℝ)^(eulerLeibnizTerms rank).length,by positivity,?_⟩
  intro curve smooth weight payment weight0 payment0 energies
  let values := fun (_ : ℕ) order radius => ‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) order curve radius‖
  have continuous (order : ℕ) : ContinuousOn (vectorEulerWithinIteratedDerivative (Icc lower 1) order curve) (Icc lower 1) :=
    (vectorEulerWithin_smooth (Icc lower 1) (uniqueDiffOn_Icc bounded) curve order 0
      (by simpa only [Nat.zero_add] using contDiffOn_infty.mp smooth order)).continuousOn
  have summed := eulerAllocationSum_squareEnergy (volume.restrict (Icc lower 1)) values payment payment0 (eulerLeibnizTerms rank)
    (fun term _ => (((continuous term.2).const_smul weight).aestronglyMeasurable (μ:=volume) measurableSet_Icc).norm)
    (by
      intro term member
      have allocated := eulerLeibnizTerms_rank rank term member
      simpa only [values,norm_norm] using energies term.2 (by omega))
  have energy : (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      ((eulerAllocationSum (fun a b => values a b radius) (eulerLeibnizTerms rank))^2)) ≤
      ENNReal.ofReal (((4:ℝ)^(eulerLeibnizTerms rank).length*payment)^2) := by
    simpa only [Real.norm_eq_abs,sq_abs] using summed
  have actual := dominated_squareEnergy (volume.restrict (Icc lower 1))
    (fun radius => weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (fun point => balancedSevenInput parameters point (curve point)) radius)
    (fun radius => eulerAllocationSum (fun a b => values a b radius) (eulerLeibnizTerms rank))
    action ((4:ℝ)^(eulerLeibnizTerms rank).length*payment) action0
    (Filter.Eventually.of_forall (fun _ => eulerAllocationSum_nonnegative _ (fun _ _ => norm_nonneg _) _)) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
      have actual := mul_le_mul_of_nonneg_left
        (bound lower positive bounded curve rank (contDiffOn_infty.mp smooth rank)
          ⟨radius,⟨positive.le.trans inside.1,inside.2⟩⟩ inside) weight0
      rw [norm_smul,Real.norm_of_nonneg weight0]
      apply actual.trans_eq
      rw [mul_left_comm,eulerAllocationSum_mul_left]
      congr 1
      congr 1
      funext first second
      dsimp only [values]
      rw [norm_smul,Real.norm_of_nonneg weight0]) energy
  exact actual.trans_eq (by congr 1; ring)

end Grad.OriginalCartesianTameEstimate
