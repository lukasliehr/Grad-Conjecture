import AUB7CompletedCutoffDifference

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter
open scoped Topology
namespace Grad.ActualUniformGlobal
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.OrdinaryDiskFaithfulness Grad.OrdinaryDiskCalculus Grad.AngularSobolevTruncation
attribute [local instance] unitNormedSpace
local instance inverseComplete (grade : ℕ) : CompleteSpace (unitDiskSobolev grade) := by
  unfold unitDiskSobolev
  infer_instance

private theorem cauchySeq_of_norm_difference_le {ι E F : Type*} [Nonempty ι] [SemilatticeSup ι]
    [NormedAddCommGroup E] [NormedAddCommGroup F] (source : ι → E) (target : ι → F)
    (constant : ℝ) (nonnegative : 0 ≤ constant) (sourceCauchy : CauchySeq source)
    (bound : ∀ first second, ‖target first - target second‖ ≤ constant * ‖source first - source second‖) :
    CauchySeq target := by
  apply Metric.cauchySeq_iff.mpr
  intro epsilon positive
  have denominator : 0 < constant + 1 := by linarith
  obtain ⟨base, tail⟩ := Metric.cauchySeq_iff.mp sourceCauchy (epsilon / (constant + 1)) (div_pos positive denominator)
  refine ⟨base, ?_⟩
  intro first firstLarge second secondLarge
  have close := (lt_div_iff₀ denominator).mp (tail first firstLarge second secondLarge)
  have estimate := bound first second
  rw [← dist_eq_norm, ← dist_eq_norm] at estimate
  nlinarith [dist_nonneg (x := source first) (y := source second)]

theorem finiteCompletedInverse_cauchy (grade : ℕ) (parameters : PhaseParameters)
    (parameter : ℝ) (source : unitDiskSobolev grade) :
    CauchySeq (fun modes : Finset ℤ => finiteCompletedInverse grade parameters parameter modes source) :=
  cauchySeq_of_norm_difference_le _ _ (finiteInverseConstant grade |parameter|)
    (finiteInverseConstant_nonnegative grade |parameter|)
    (ordinarySelected_tendsto parameters grade source).cauchy_map
    (fun first second => finiteCompletedInverse_difference_bound grade |parameter| parameters parameter le_rfl first second source)

theorem actualCompletedInverseValue_exists (grade : ℕ) (parameters : PhaseParameters)
    (parameter : ℝ) (source : unitDiskSobolev grade) :
    ∃ solution : unitDiskSobolev (grade + 2),
      Tendsto (fun modes : Finset ℤ => finiteCompletedInverse grade parameters parameter modes source) atTop (𝓝 solution) :=
  cauchy_map_iff_exists_tendsto.mp (finiteCompletedInverse_cauchy grade parameters parameter source)

def actualCompletedInverseValue (grade : ℕ) (parameters : PhaseParameters)
    (parameter : ℝ) (source : unitDiskSobolev grade) : unitDiskSobolev (grade + 2) :=
  (actualCompletedInverseValue_exists grade parameters parameter source).choose

theorem actualCompletedInverseValue_tendsto (grade : ℕ) (parameters : PhaseParameters)
    (parameter : ℝ) (source : unitDiskSobolev grade) :
    Tendsto (fun modes : Finset ℤ => finiteCompletedInverse grade parameters parameter modes source) atTop
      (𝓝 (actualCompletedInverseValue grade parameters parameter source)) :=
  (actualCompletedInverseValue_exists grade parameters parameter source).choose_spec

def fullWeakBulkOperator (parameter : ℝ) : DiskL2 1 →L[ℂ] DiskL2 1 :=
  highDiskBulk.comp ((highRobinWeakInverse parameter).comp highL2ProjectionInto)

/-- The strong Sobolev limit is the very same previously constructed weak
inverse, with literal full-disk bulk; no replacement solution is introduced. -/
theorem actualCompletedInverseValue_bulk (grade : ℕ) (parameters : PhaseParameters)
    (parameter : ℝ) (source : unitDiskSobolev grade) :
    unitDiskBulk (grade + 2) (actualCompletedInverseValue grade parameters parameter source) =
      fullWeakBulkOperator parameter (unitDiskBulk grade source) := by
  have first := ((unitDiskBulk (grade + 2)).continuous.tendsto _).comp
    (actualCompletedInverseValue_tendsto grade parameters parameter source)
  have second := ((fullWeakBulkOperator parameter).continuous.tendsto _).comp
    (diskSelectedModes_tendsto (unitDiskBulk grade source))
  have equality (modes : Finset ℤ) :
      unitDiskBulk (grade + 2) (finiteCompletedInverse grade parameters parameter modes source) =
        fullWeakBulkOperator parameter (diskSelectedModes modes (unitDiskBulk grade source)) := by
    exact (finiteCompletedInverse_bulk grade parameters parameter modes source).trans
      (congrArg (fun field : highDiskL2 => highDiskBulk (highRobinWeakInverse parameter field))
        (highL2ProjectionInto_selected modes (unitDiskBulk grade source)).symm)
  exact tendsto_nhds_unique (first.congr' (Eventually.of_forall equality)) second

theorem actualCompletedInverseValue_bound (grade : ℕ) (ceiling : ℝ) (parameters : PhaseParameters)
    (parameter : ℝ) (bounded : |parameter| ≤ ceiling) (source : unitDiskSobolev grade) :
    ‖actualCompletedInverseValue grade parameters parameter source‖ ≤ finiteInverseConstant grade ceiling * ‖source‖ :=
  le_of_tendsto (continuous_norm.tendsto _ |>.comp
    (actualCompletedInverseValue_tendsto grade parameters parameter source))
    (Eventually.of_forall (fun modes => finiteCompletedInverse_uniform grade ceiling parameters parameter bounded modes source))

end Grad.ActualUniformGlobal
