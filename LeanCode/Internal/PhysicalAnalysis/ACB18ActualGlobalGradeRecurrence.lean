import ACB17ActualInteriorPartition

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterBounds
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.ActualCenterVolterra Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.ActualInverseInduction Grad.InteriorLocalization Grad.OrdinaryDiskCalculus
open Grad.OrdinaryInteriorBootstrap
open Grad.NonlinearDivision (laplacianJet)
open Grad.GaugeCoefficients.Physical.RadialLedger (apLoweringConstant apLoweringConstant_nonnegative)
local instance (priority := 2000) centerNativeUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade

private theorem native_linear_residual_bound {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (linear : V →ₗ[ℂ] W)
    (field source residual : V) (scalar : ℂ) (ceiling : ℝ)
    (equation : residual = -source - scalar • field) (bound : ‖scalar‖ ≤ ceiling) :
    ‖linear residual‖ ≤ ceiling * ‖linear field‖ + ‖linear source‖ := by
  rw [equation, map_sub, map_neg, map_smul]
  exact (norm_sub_le _ _).trans ((add_le_add (le_of_eq (norm_neg _))
    ((le_of_eq (norm_smul _ _)).trans (mul_le_mul_of_nonneg_right bound (norm_nonneg _)))).trans_eq (add_comm _ _))

theorem pinnedCenter_laplacian_native (grade : ℕ) (radius : ℝ) (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (frequency : ℝ) (bounded : |frequency| ≤ radius) (source : ClosedJet 1)
    (pure : angularClosedJet mode source = source) :
    ‖unitDiskCoreInto grade (laplacianJet (pinnedCenterSolution mode frequency source))‖ ≤
      3 * radius ^ 2 * ‖unitDiskCoreInto grade (pinnedCenterSolution mode frequency source)‖ +
        ‖unitDiskCoreInto grade source‖ := by
  have equation : laplacianJet (pinnedCenterSolution mode frequency source) =
      -source - ((3 * frequency ^ 2 : ℝ) : ℂ) • pinnedCenterSolution mode frequency source :=
    (eq_sub_iff_add_eq).mpr (pinnedCenterSolution_equation mode center frequency source pure)
  have scalar : ‖((3 * frequency ^ 2 : ℝ) : ℂ)‖ ≤ 3 * radius ^ 2 := by
    have square := pow_le_pow_left₀ (abs_nonneg frequency) bounded 2
    rw [sq_abs] at square
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 3 * frequency ^ 2)]
    nlinarith
  exact @native_linear_residual_bound (ClosedJet 1) (unitDiskSobolev grade)
    inferInstance inferInstance inferInstance (unitNormedSpace grade)
    (unitDiskCoreInto grade) _ _ _ _ _ equation scalar

def centerGlobalStateConstant (order : ℕ) (radius : ℝ) : ℝ :=
  max 0 (ordinaryInteriorSourceConstant order * (3 * radius ^ 2 * apLoweringConstant order) +
    ordinaryInteriorStateConstant order)

theorem centerGlobalStateConstant_nonnegative (order : ℕ) (radius : ℝ) : 0 ≤ centerGlobalStateConstant order radius :=
  le_max_left _ _

def centerGlobalSourceConstant (grade : ℕ) (large : 3 ≤ grade) (radius : ℝ) (order : ℕ) : ℝ :=
  ordinaryInteriorSourceConstant order * apLoweringConstant order + centerOuterConstant grade large radius (order + 2)

theorem centerGlobalSourceConstant_nonnegative (grade : ℕ) (large : 3 ≤ grade) (radius : ℝ) (order : ℕ) :
    0 ≤ centerGlobalSourceConstant grade large radius order :=
  add_nonneg (mul_nonneg (interiorSourceConstant_nonnegative order) (apLoweringConstant_nonnegative order))
    (centerOuterConstant_nonnegative grade large radius (order + 2))

private theorem native_recurrence_organize (value state source sourceFactor stateFactor parameter lowerState lowerSource outer : ℝ)
    (stateNonnegative : 0 ≤ state)
    (bound : value ≤ (sourceFactor * (parameter * (lowerState * state) + lowerSource * source) + stateFactor * state) + outer * source) :
    value ≤ max 0 (sourceFactor * (parameter * lowerState) + stateFactor) * state +
      (sourceFactor * lowerSource + outer) * source := by
  have organized : value ≤ (sourceFactor * (parameter * lowerState) + stateFactor) * state +
      (sourceFactor * lowerSource + outer) * source := bound.trans_eq (by ring)
  exact organized.trans (add_le_add (mul_le_mul_of_nonneg_right (le_max_right _ _) stateNonnegative) le_rfl)

/-- The exact global native grade step glues the actual inner and outer
cutoffs of the same pinned solution. Every source row remains paid by Hs. -/
theorem pinnedCenter_global_step (grade : ℕ) (large : 3 ≤ grade) (radius : ℝ)
    (mode : ℤ) (center : mode = 1 ∨ mode = -1) (frequency : ℝ) (bounded : |frequency| ≤ radius)
    (source : ClosedJet 1) (pure : angularClosedJet mode source = source) (order : ℕ) (paid : order ≤ grade) :
    ‖unitDiskCoreInto (order + 2) (pinnedCenterSolution mode frequency source)‖ ≤
      centerGlobalStateConstant order radius * ‖unitDiskCoreInto (order + 1) (pinnedCenterSolution mode frequency source)‖ +
        centerGlobalSourceConstant grade large radius order * ‖unitDiskCoreInto grade source‖ := by
  let solution := pinnedCenterSolution mode frequency source
  have split := ((unitDiskCoreInto (order + 2)).map_add
    (centerInnerJet mode solution) (centerOuterJet mode solution)).symm.trans
      (congrArg (unitDiskCoreInto (order + 2)) (center_partition mode solution))
  have laplacian := (pinnedCenter_laplacian_native order radius mode center frequency bounded source pure).trans
    (add_le_add (mul_le_mul_of_nonneg_left (originalCore_lower (Nat.le_succ order) solution) (by positivity))
      (originalCore_lower paid source))
  have inner := (centerInner_native_estimate order mode solution
    (pinnedCenterSolution_pure mode center frequency source pure)).trans
      (add_le_add (mul_le_mul_of_nonneg_left laplacian (interiorSourceConstant_nonnegative order)) le_rfl)
  have outer := pinnedCenter_outer_native grade large radius mode center frequency bounded source pure (order + 2) (by omega)
  have combined := (norm_add_le (unitDiskCoreInto (order + 2) (centerInnerJet mode solution))
    (unitDiskCoreInto (order + 2) (centerOuterJet mode solution))).trans (add_le_add inner outer)
  exact native_recurrence_organize _ _ _ _ _ _ _ _ _ (norm_nonneg _)
    ((congrArg norm split).symm.le.trans combined)

end Grad.ActualCenterBounds
