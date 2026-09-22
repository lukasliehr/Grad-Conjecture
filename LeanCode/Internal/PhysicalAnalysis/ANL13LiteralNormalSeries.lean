import ANL12HighNormalLift

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal
namespace Grad.CircularNormalLift
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift Grad.Constraints
open Grad.CircularHighWeak Grad.OrdinaryDiskCalculus
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.RadialLedger
local instance (priority := 2000) seriesUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade
local instance (priority := 2000) seriesBoundarySpace (grade : ℕ) : NormedSpace ℂ (normalBoundaryGrade grade) :=
  (normalBoundaryGrade grade).normedSpace

theorem normalBoundary_modes_hasSum (grade : ℕ) (field : normalBoundaryGrade grade) :
    HasSum (fun mode => normalBoundaryInto grade
      (Finsupp.single mode (normalBoundaryCoefficient grade field mode))) field := by
  have raw := lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) field.val
  have collapsed : HasSum (fun mode : ℤ => lp.single (E := fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 (mode, 0) (field.val (mode, 0))) field.val := by
    apply raw.prod_fiberwise
    intro mode
    have equality (cell : ℤ) : lp.single (E := fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 (mode, cell) (field.val (mode, cell)) =
        if cell = 0 then lp.single (E := fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 (mode, 0) (field.val (mode, 0)) else 0 := by
      by_cases isZero : cell = 0
      · subst cell
        rw [if_pos rfl]
      · rw [if_neg isZero, normalBoundary_cell_zero grade field mode cell isZero, lp.single_zero]
    exact (hasSum_ite_eq 0 _).congr_fun equality
  have inducing : Topology.IsInducing (normalBoundaryGrade grade).subtypeL := Topology.IsInducing.subtypeVal
  apply (inducing.hasSum_iff _ _).mp
  have expression : ((normalBoundaryGrade grade).subtypeL ∘ (fun mode => normalBoundaryInto grade
      (Finsupp.single mode (normalBoundaryCoefficient grade field mode)))) =
        (fun mode => lp.single (E := fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 (mode, 0) (field.val (mode, 0))) := by
    funext mode
    exact normalBoundaryAmbient_single grade mode (field.val (mode, 0))
  rw [expression]
  exact collapsed

def normalDiskValue (grade : ℕ) (large : 2 ≤ grade) :
    unitDiskSobolev grade →L[ℂ] C(ClosedDisk, ComplexEuclidean 1) :=
  (apWeightedDerivative (dimension := 1) (grade := grade) 1 0 0 1
    (order := 0) large 0 emptyCartesianWord).comp (unitDiskSobolev grade).subtypeL

theorem normalDiskValue_core (grade : ℕ) (large : 2 ≤ grade) (core : ClosedJet 1) :
    normalDiskValue grade large (unitDiskCoreInto grade core) = core.value := by
  change apWeightedDerivative (dimension := 1) (grade := grade) 1 0 0 1
    (order := 0) large 0 emptyCartesianWord (apFiniteInto 1 0 0 1 (Finsupp.single 0 core)) = _
  rw [apWeightedDerivative_core, Finsupp.single_eq_same, unweightedJet, closedDerivative_zero_order]

theorem normalDiskValue_mode (grade : ℕ) (large : 2 ≤ grade) (mode : ℤ) (value : ComplexEuclidean 1) :
    normalDiskValue grade large (completedNormalLift grade (normalBoundaryInto grade (Finsupp.single mode value))) =
      (normalModeJetLinear mode value).value := by
  have finite := congrArg (fun field : unitDiskSobolev grade => normalDiskValue grade large field)
    (completedNormalLift_finite grade large (Finsupp.single mode value))
  have single : finiteNormalLinear (Finsupp.single mode value) = normalModeJetLinear mode value := by
    simp [finiteNormalLinear]
  exact finite.trans ((normalDiskValue_core grade large _).trans (congrArg (fun core : ClosedJet 1 => core.value) single))

theorem normalSmoothLift_value_hasSum (parameters : PhaseParameters) (data : NormalSmoothBoundary) :
    HasSum (fun mode => (normalModeJetLinear mode (normalBoundaryCoefficient 2 (data.grade 0) mode)).value)
      (normalSmoothLift parameters data).value := by
  have boundary := normalBoundary_modes_hasSum 2 (data.grade 0)
  have lifted := (completedNormalLift 2).hasSum boundary
  have values := (normalDiskValue 2 (by omega)).hasSum lifted
  have limit : normalDiskValue 2 (by omega) (completedNormalLift 2 (data.grade 0)) =
      (normalSmoothLift parameters data).value :=
    (congrArg (normalDiskValue 2 (by omega)) (normalSmoothLift_core parameters data 0)).symm.trans
      (normalDiskValue_core 2 (by omega) (normalSmoothLift parameters data))
  rw [limit] at values
  have expression : (fun mode => normalDiskValue 2 (by omega) (completedNormalLift 2
      (normalBoundaryInto 2 (Finsupp.single mode (normalBoundaryCoefficient 2 (data.grade 0) mode))))) =
      (fun mode => (normalModeJetLinear mode (normalBoundaryCoefficient 2 (data.grade 0) mode)).value) := by
    funext mode
    exact normalDiskValue_mode 2 (by omega) mode (normalBoundaryCoefficient 2 (data.grade 0) mode)
  change HasSum (fun mode => normalDiskValue 2 (by omega) (completedNormalLift 2
      (normalBoundaryInto 2 (Finsupp.single mode (normalBoundaryCoefficient 2 (data.grade 0) mode))))) _ at values
  rw [expression] at values
  exact values

/-- The completed smooth lift is the literal AN22 kernel series at every closed-disk point. -/
theorem normalSmoothLift_point_series (parameters : PhaseParameters) (data : NormalSmoothBoundary) (point : ClosedDisk) :
    (normalSmoothLift parameters data).value point =
      ∑' mode : ℤ, normalKernel mode point.val • normalBoundaryCoefficient 2 (data.grade 0) mode := by
  have evaluated := (ContinuousMap.evalCLM ℂ point).hasSum (normalSmoothLift_value_hasSum parameters data)
  exact evaluated.tsum_eq.symm

theorem normalSmoothLift_zero_inner (parameters : PhaseParameters) (data : NormalSmoothBoundary)
    (point : ClosedDisk) (inside : ‖point.val‖ ≤ (7 / 8 : ℝ)) :
    (normalSmoothLift parameters data).value point = 0 := by
  rw [normalSmoothLift_point_series]
  simp only [normalKernel_zero_inner _ point.val inside, zero_smul, tsum_zero]

theorem normalSmoothLift_polar_series (parameters : PhaseParameters) (data : NormalSmoothBoundary)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (beforeAxis : time < 1) (angle : CellCircle) :
    (normalSmoothLift parameters data).value
      ⟨(1 - time) • boundaryCirclePoint angle, by
        change ‖(1 - time) • boundaryCirclePoint angle‖ ≤ 1
        rw [norm_smul, boundaryCirclePoint_norm, mul_one, Real.norm_of_nonneg (sub_pos.mpr beforeAxis).le]
        linarith⟩ =
      ∑' mode : ℤ, (((-time * collarCutoff1D time * Real.exp (-boundaryFrequency (mode, 0) * time) : ℝ) : ℂ) *
        fourier mode angle) • normalBoundaryCoefficient 2 (data.grade 0) mode := by
  rw [normalSmoothLift_point_series]
  apply tsum_congr
  intro mode
  rw [normalKernel_polar mode time beforeAxis]
  have scalar : normalProfile mode time = -time * collarCutoff1D time * Real.exp (-boundaryFrequency (mode, 0) * time) := by
    unfold normalProfile cutoffExponentialProfile
    ring
  rw [scalar]

end Grad.CircularNormalLift
