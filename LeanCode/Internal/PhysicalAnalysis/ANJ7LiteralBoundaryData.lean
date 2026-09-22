import ANJ6SmoothInhomogeneousInverse

noncomputable section
set_option maxHeartbeats 1200000
open Set
open scoped Topology
namespace Grad.InhomogeneousHighRobin
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.OrdinaryDiskCalculus Grad.CircularNormalLift Grad.ActualSmoothRobin Grad.BoundaryTrace
open Grad.Constraints Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.WeightedTrace
local instance (priority := 2000) boundaryDataUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade
local instance (priority := 2000) boundaryDataBoundarySpace (grade : ℕ) : NormedSpace ℂ (normalBoundaryGrade grade) :=
  (normalBoundaryGrade grade).normedSpace

theorem normalBoundary_ext (grade : ℕ) (first second : normalBoundaryGrade grade)
    (same : ∀ mode, normalBoundaryCoefficient grade first mode = normalBoundaryCoefficient grade second mode) :
    first = second := by
  apply Subtype.ext
  apply lp.ext
  funext output
  by_cases cellZero : output.2 = 0
  · have pair : output = (output.1, 0) := Prod.ext rfl cellZero
    rw [pair]
    exact (apBoundary_weighted_coefficient 1 0 0 1 (grade - 1) first.val (output.1, 0)).symm.trans
      ((congrArg (fun value : ComplexEuclidean 1 => (normalBoundaryWeight grade output.1 : ℂ) • value)
        (same output.1)).trans (apBoundary_weighted_coefficient 1 0 0 1 (grade - 1) second.val (output.1, 0)))
  · exact (normalBoundary_cell_zero grade first output.1 output.2 cellZero).trans
      (normalBoundary_cell_zero grade second output.1 output.2 cellZero).symm

/-- Ordinary boundary restriction of an actual smooth disk jet, with the
original half-order boundary norm. -/
def boundaryJetGrade (order : ℕ) (core : ClosedJet 1) : normalBoundaryGrade (order + 2) :=
  ⟨ordinaryBoundaryTrace (order + 1) (by omega) (unitDiskCoreInto (order + 1) core), by
    apply (normalBoundary_mem_iff (order + 2) _).2
    intro mode cell different
    rw [← apBoundary_weighted_coefficient 1 0 0 1 (order + 1) _ (mode, cell),
      ordinaryBoundaryTrace_core_coefficient, if_neg different, smul_zero]⟩

theorem boundaryJetGrade_coefficient (order : ℕ) (core : ClosedJet 1) (mode : ℤ) :
    normalBoundaryCoefficient (order + 2) (boundaryJetGrade order core) mode =
      fourierCoeff (fun angle : CellCircle => core.value (boundaryDiskPoint angle)) mode :=
  (ordinaryBoundaryTrace_core_coefficient (order + 1) (by omega) core (mode, 0)).trans (if_pos rfl)

def boundaryJetData (core : ClosedJet 1) : NormalSmoothBoundary where
  grade order := boundaryJetGrade order core
  coherent order := by
    apply normalBoundary_ext
    intro mode
    exact (normalBoundaryLower_coefficient 2 (order + 2) (by omega) (by omega) _ mode).trans
      ((boundaryJetGrade_coefficient order core mode).trans (boundaryJetGrade_coefficient 0 core mode).symm)

theorem ordinaryBoundaryTrace_zero_implies_boundary (grade : ℕ) (positive : 1 ≤ grade) (core : ClosedJet 1)
    (zeroTrace : ordinaryBoundaryTrace grade positive (unitDiskCoreInto grade core) = 0) :
    ∀ angle, core.value (boundaryDiskPoint angle) = 0 := by
  apply closedBoundary_zero_of_coefficients
  intro mode
  have coefficient := congrArg (fun field => apBoundaryCoefficient 1 0 0 1 grade field (mode, 0)) zeroTrace
  rw [ordinaryBoundaryTrace_core_coefficient, if_pos rfl] at coefficient
  exact coefficient.trans (smul_zero _)

/-- Literal prescribed Robin values for an arbitrary actual smooth boundary
restriction. The solution is the same one used at every Sobolev grade. -/
theorem inhomogeneousSmoothInverse_boundary_value (parameters : PhaseParameters) (parameter : ℝ)
    (core boundary : ClosedJet 1) (angle : CellCircle) :
    (robinResidualJet (inhomogeneousSmoothInverse parameters parameter core (boundaryJetData boundary))).value
      (boundaryDiskPoint angle) = boundary.value (boundaryDiskPoint angle) := by
  let solution := inhomogeneousSmoothInverse parameters parameter core (boundaryJetData boundary)
  let mapping : ClosedJet 1 →ₗ[ℂ] APBoundaryGrade 1 0 0 1 1 1 :=
    (ordinaryBoundaryTrace 1 (by omega)).toLinearMap.comp (unitDiskCoreInto 1)
  have same : mapping (robinResidualJet solution) = mapping boundary :=
    (ordinaryRobinTrace_core 0 solution).symm.trans
      (inhomogeneousSmoothInverse_robin_trace parameters parameter core (boundaryJetData boundary) 0)
  have zeroTrace : mapping (robinResidualJet solution - boundary) = 0 :=
    (mapping.map_sub _ _).trans ((congrArg (fun value => value - mapping boundary) same).trans (sub_self _))
  have value := ordinaryBoundaryTrace_zero_implies_boundary 1 (by omega)
    (robinResidualJet solution - boundary) zeroTrace angle
  simp only [sub_eq_add_neg, closedJet_value_add, closedJet_value_neg, ContinuousMap.add_apply, ContinuousMap.neg_apply] at value
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using value)

theorem inhomogeneousSmoothInverse_pointwise_robin (parameters : PhaseParameters) (parameter : ℝ)
    (core boundary : ClosedJet 1) (angle : CellCircle) :
    fderiv ℝ (smoothClosedExtension (inhomogeneousSmoothInverse parameters parameter core (boundaryJetData boundary)))
      (boundaryCirclePoint angle) (boundaryCirclePoint angle) +
      (2 : ℝ) • (inhomogeneousSmoothInverse parameters parameter core (boundaryJetData boundary)).value (boundaryDiskPoint angle) =
        boundary.value (boundaryDiskPoint angle) := by
  have value := inhomogeneousSmoothInverse_boundary_value parameters parameter core boundary angle
  unfold robinResidualJet at value
  rw [closedJet_value_add, ContinuousMap.add_apply, closedJet_value_smul, ContinuousMap.smul_apply,
    eulerJet_extension_value] at value
  exact value

end Grad.InhomogeneousHighRobin
