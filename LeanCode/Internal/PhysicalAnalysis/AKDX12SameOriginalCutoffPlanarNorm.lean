import AKDX11SameCutoffClosedJet

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.OriginalCollarNorm
open Grad.Constraints Grad.ClosedJets Grad.CartesianState Grad.CartesianStartup
open Grad.OriginalCoreRealization Grad.ActualOriginalSourceMoments Grad.OriginalCartesianTameEstimate
open Grad.BoundaryTrace Grad.BoundaryLift
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger

/-- Finite-support bounds pass to the exact infinite-cell original planar
norm of the SAME cutoff core. No frequency truncation or changed width enters. -/
theorem sameOriginalCutoff_planarNorm (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (cutoff : SpatialPlane→ℝ) (smooth : ContDiff ℝ ∞ cutoff) (compact : HasCompactSupport cutoff)
    (vanishes : ∀ point,‖point‖<2*lower → cutoff point=0) (grade : ℕ) :
    ∃ constant : ℝ,0≤constant ∧ ∀ (parameters : PhaseParameters) (core image : ACore parameters 3),
      (originalSourceMoments parameters image).field=
        startupCutoffL2 cutoff smooth compact (originalSourceMoments parameters core).field →
      ∀ payment : ℝ,0≤payment →
      (∀ cells : Finset ℤ,(∑ cell∈cells,fixedCollarIntegral lower
        (polarJetSquaredDensity
          (smoothClosedExtension (phaseWeightedJet parameters cell (core.val cell)) ∘ collarPlane) grade))≤payment^2) →
      originalPlanarNorm parameters grade image≤constant*payment := by
  let result := fixedCutoff_massRow_energy lower positive bounded cutoff smooth vanishes grade
  let rowConstant := result.choose
  have rowConstant0 : 0≤rowConstant := result.choose_spec.1
  refine ⟨Real.sqrt rowConstant,Real.sqrt_nonneg _,?_⟩
  intro parameters core image same payment payment0 energy
  have finiteBound (cells : Finset ℤ) :
      (∑ cell∈cells,‖apMassRow 1 grade (phaseWeightedJet parameters cell (image.val cell))‖^2)≤
        rowConstant*payment^2 := by
    calc
      _ ≤ ∑ cell∈cells,rowConstant*fixedCollarIntegral lower
          (polarJetSquaredDensity
            (smoothClosedExtension (phaseWeightedJet parameters cell (core.val cell)) ∘ collarPlane) grade) := by
        apply Finset.sum_le_sum
        intro cell _
        rw [sameOriginalCutoff_closedJet parameters cutoff smooth compact core image same cell]
        exact result.choose_spec.2 3 _ (smoothClosedExtension_smooth _)
      _ = rowConstant*(∑ cell∈cells,fixedCollarIntegral lower
          (polarJetSquaredDensity
            (smoothClosedExtension (phaseWeightedJet parameters cell (core.val cell)) ∘ collarPlane) grade)) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (energy cells) rowConstant0
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) payment0)).mp
  change originalPlanarNorm parameters grade image^2≤(Real.sqrt rowConstant*payment)^2
  rw [originalPlanarNorm_sq,mul_pow,Real.sq_sqrt rowConstant0]
  exact (originalPlanarNorm_summable parameters grade image).tsum_le_of_sum_le finiteBound

end Grad.OriginalCollarNorm
