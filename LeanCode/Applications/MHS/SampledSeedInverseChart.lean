import SampledSeedPerturbation

noncomputable section

open Set
open scoped ContDiff

namespace Grad.PhysicalFamily.SampledGlobalEmbedding

open Grad.MainTarget Grad.PhysicalFamily Grad.GeometryClosure
open Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledAllTimeBounds
open Grad.MainAssembly.PhysicalNormalHessian
open Grad.MainAssembly.SampledAxisBasics
open Matrix

def seedCoverChart (family : CellSolutionFamily cellLength) (parameter : ℝ) (point : Vec) : Vec :=
  coordinateDirection (seedAction family.rho family.alpha family.delta parameter
    (point 2) (planarPart point)) (point 2)

def seedInverseCoverChart (family : CellSolutionFamily cellLength) (parameter : ℝ)
    (point : Vec) : Vec :=
  coordinateDirection
    (WithLp.toLp 2 (Matrix.mulVec
      (seedInverse family.rho (seedAngle family.alpha family.delta parameter (point 2)))
      (fun coordinate => (planarPart point) coordinate)) : Plane) (point 2)

theorem seedCoverChart_contDiff (family : CellSolutionFamily cellLength) :
    ContDiff ℝ ∞ (fun argument : ℝ × Vec => seedCoverChart family argument.1 argument.2) := by
  rw [contDiff_piLp]
  intro coordinate
  fin_cases coordinate <;>
    simp [seedCoverChart, coordinateDirection, seedAction, harmonicSeedMatrix,
      seedMatrix, rotatedDiagonal_entries, planarPart, vector, seedAngle] <;> fun_prop

theorem seedInverseCoverChart_contDiff (family : CellSolutionFamily cellLength) :
    ContDiff ℝ ∞ (fun argument : ℝ × Vec => seedInverseCoverChart family argument.1 argument.2) := by
  rw [contDiff_piLp]
  intro coordinate
  fin_cases coordinate <;>
    simp [seedInverseCoverChart, coordinateDirection, seedInverse,
      rotatedDiagonal_entries, planarPart, vector, seedAngle] <;> fun_prop

theorem seedInverseCoverChart_seedCoverChart (family : CellSolutionFamily cellLength)
    (parameter : ℝ) (point : Vec) :
    seedInverseCoverChart family parameter (seedCoverChart family parameter point) = point := by
  have matrixIdentity := (seed_inverse_identities
    (by linarith [family.rhoPositive] : -1 < family.rho)
    (by linarith [family.rhoSmall] : family.rho < 1)
    (seedAngle family.alpha family.delta parameter (point 2))).1
  have planarIdentity :
      (WithLp.toLp 2 (Matrix.mulVec
        (seedInverse family.rho (seedAngle family.alpha family.delta parameter (point 2)))
        (fun coordinate => (seedAction family.rho family.alpha family.delta parameter
          (point 2) (planarPart point)) coordinate)) : Plane) = planarPart point := by
    ext coordinate
    change ((seedInverse family.rho (seedAngle family.alpha family.delta parameter (point 2))) *ᵥ
      ((seedMatrix family.rho (seedAngle family.alpha family.delta parameter (point 2))) *ᵥ
        (fun coordinate => (planarPart point) coordinate))) coordinate = _
    rw [Matrix.mulVec_mulVec, matrixIdentity, Matrix.one_mulVec]
  unfold seedInverseCoverChart seedCoverChart
  rw [planarPart_coordinateDirection, coordinateDirection_time, planarIdentity]
  exact coordinateDirection_planarPart point

theorem seedInverseCoverChart_periodic_shift (family : CellSolutionFamily cellLength)
    (parameter : ℝ) (point : Vec) :
    seedInverseCoverChart family parameter (point + physicalToroidalCLM (2 * Real.pi)) =
      seedInverseCoverChart family parameter point + physicalToroidalCLM (2 * Real.pi) := by
  have phase : seedAngle family.alpha family.delta parameter
      ((point + physicalToroidalCLM (2 * Real.pi)) 2) =
      seedAngle family.alpha family.delta parameter (point 2) := by
    change seedAngle family.alpha family.delta parameter (point 2 + 2 * Real.pi) = _
    apply seedAngle_periodic_shift
    exact ⟨1, by ring⟩
  have planar : planarPart (point + physicalToroidalCLM (2 * Real.pi)) = planarPart point := by
    ext coordinate
    fin_cases coordinate <;> simp [planarPart, physicalToroidalCLM_apply, coordinateDirection, vector]
  unfold seedInverseCoverChart
  rw [phase, planar]
  ext coordinate
  fin_cases coordinate <;> simp [physicalToroidalCLM_apply, coordinateDirection, vector]

theorem fderiv_translation
    {Source Target : Type*} [NormedAddCommGroup Source] [NormedSpace ℝ Source]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (mapping : Source → Target) (sourceShift : Source) (targetShift : Target)
    (differentiable : Differentiable ℝ mapping)
    (translation : ∀ point, mapping (point + sourceShift) = mapping point + targetShift)
    (point : Source) :
    fderiv ℝ mapping (point + sourceShift) = fderiv ℝ mapping point := by
  have shiftDerivative : HasFDerivAt (fun value : Source => value + sourceShift)
      (ContinuousLinearMap.id ℝ Source) point := by
    exact ((hasFDerivAt_id (𝕜 := ℝ) point).add
      (hasFDerivAt_const (x := point) sourceShift)).congr_fderiv (add_zero _)
  have chain := ((differentiable (point + sourceShift)).hasFDerivAt.comp point shiftDerivative).fderiv
  have targetDerivative := ((differentiable point).hasFDerivAt.add
    (hasFDerivAt_const (x := point) targetShift)).fderiv
  change fderiv ℝ (fun value => mapping value + targetShift) point =
    fderiv ℝ mapping point + 0 at targetDerivative
  have identity : (fun value => mapping (value + sourceShift)) =
      (fun value => mapping value + targetShift) := funext translation
  change fderiv ℝ (fun value => mapping (value + sourceShift)) point = _ at chain
  rw [identity, targetDerivative] at chain
  simpa using chain.symm

theorem parameter_fderiv_contDiff
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (mapping : ℝ → Vec → Target)
    (smooth : ContDiff ℝ ∞ (Function.uncurry mapping)) :
    ContDiff ℝ ∞ (fun argument : ℝ × Vec => fderiv ℝ (mapping argument.1) argument.2) := by
  have duplication : ContDiff ℝ ∞
      (fun argument : (ℝ × Vec) × Vec => (argument.1.1, argument.2)) := by fun_prop
  exact (smooth.comp duplication).fderiv contDiff_snd (by simp)

def inverseChartJet (family : CellSolutionFamily cellLength) (argument : ℝ × Vec) :
    (Vec →L[ℝ] Vec) × (Vec →L[ℝ] Vec →L[ℝ] Vec) :=
  (fderiv ℝ (seedInverseCoverChart family argument.1) argument.2,
    fderiv ℝ (fderiv ℝ (seedInverseCoverChart family argument.1)) argument.2)

theorem inverseChartJet_contDiff (family : CellSolutionFamily cellLength) :
    ContDiff ℝ ∞ (inverseChartJet family) := by
  have first := parameter_fderiv_contDiff (seedInverseCoverChart family)
    (seedInverseCoverChart_contDiff family)
  exact first.prodMk (parameter_fderiv_contDiff
    (fun parameter => fderiv ℝ (seedInverseCoverChart family parameter)) first)

theorem inverseChartJet_periodic (family : CellSolutionFamily cellLength)
    (parameter : ℝ) (point : Plane) :
    Function.Periodic (fun time => inverseChartJet family
      (parameter, coordinateDirection point time)) (2 * Real.pi) := by
  have insertionSmooth : ContDiff ℝ ∞ (fun point : Vec => (parameter, point)) :=
    contDiff_const.prodMk contDiff_id
  have smooth : ContDiff ℝ ∞ (seedInverseCoverChart family parameter) :=
    (seedInverseCoverChart_contDiff family).comp
      (f := fun point : Vec => (parameter, point)) insertionSmooth
  have first : ∀ argument : Vec,
      fderiv ℝ (seedInverseCoverChart family parameter)
          (argument + physicalToroidalCLM (2 * Real.pi)) =
        fderiv ℝ (seedInverseCoverChart family parameter) argument :=
    fderiv_translation (seedInverseCoverChart family parameter)
      (physicalToroidalCLM (2 * Real.pi)) (physicalToroidalCLM (2 * Real.pi))
      (smooth.differentiable (by simp)) (seedInverseCoverChart_periodic_shift family parameter)
  have derivativeSmooth : ContDiff ℝ ∞ (fderiv ℝ (seedInverseCoverChart family parameter)) :=
    smooth.fderiv_right (by simp)
  have derivativeShift : ∀ argument : Vec,
      fderiv ℝ (seedInverseCoverChart family parameter)
          (argument + physicalToroidalCLM (2 * Real.pi)) =
        fderiv ℝ (seedInverseCoverChart family parameter) argument + 0 := by
    intro argument
    exact (first argument).trans (add_zero _).symm
  have second : ∀ argument : Vec,
      fderiv ℝ (fderiv ℝ (seedInverseCoverChart family parameter))
          (argument + physicalToroidalCLM (2 * Real.pi)) =
        fderiv ℝ (fderiv ℝ (seedInverseCoverChart family parameter)) argument :=
    fderiv_translation (fderiv ℝ (seedInverseCoverChart family parameter))
      (physicalToroidalCLM (2 * Real.pi)) (0 : Vec →L[ℝ] Vec)
      (derivativeSmooth.differentiable (by simp)) derivativeShift
  intro time
  have shift : coordinateDirection point (time + 2 * Real.pi) =
      coordinateDirection point time + physicalToroidalCLM (2 * Real.pi) := by
    ext coordinate
    fin_cases coordinate <;> simp [physicalToroidalCLM_apply, coordinateDirection, vector]
  change (fderiv ℝ (seedInverseCoverChart family parameter) _,
      fderiv ℝ (fderiv ℝ (seedInverseCoverChart family parameter)) _) = _
  rw [shift]
  exact Prod.ext (first _) (second _)

def inverseChartCompactDomain (family : CellSolutionFamily cellLength) : Set (ℝ × Vec) :=
  Icc family.lower family.upper ×ˢ
    ((fun argument : Plane × ℝ => coordinateDirection argument.1 argument.2) ''
      (Metric.closedBall (0 : Plane) 6 ×ˢ Icc (0 : ℝ) (2 * Real.pi)))

theorem inverseChartCompactDomain_isCompact (family : CellSolutionFamily cellLength) :
    IsCompact (inverseChartCompactDomain family) := by
  have coordinateSmooth : ContDiff ℝ ∞ (fun argument : Plane × ℝ =>
      coordinateDirection argument.1 argument.2) := by
    rw [contDiff_piLp]
    intro coordinate
    fin_cases coordinate <;> simp [coordinateDirection, vector] <;> fun_prop
  exact isCompact_Icc.prod (((isCompact_closedBall (0 : Plane) 6).prod isCompact_Icc).image
    coordinateSmooth.continuous)

theorem exists_seedInverseCoverChart_bounds (family : CellSolutionFamily cellLength) :
    ∃ bound : ℝ, 1 ≤ bound ∧
      ∀ (parameter : Icc family.lower family.upper) (point : Vec), ‖planarPart point‖ ≤ 6 →
        ‖fderiv ℝ (seedInverseCoverChart family parameter.val) point‖ ≤ bound ∧
        ‖fderiv ℝ (fderiv ℝ (seedInverseCoverChart family parameter.val)) point‖ ≤ bound := by
  obtain ⟨rawBound, rawBoundUpper⟩ := (inverseChartCompactDomain_isCompact family).bddAbove_image
    (inverseChartJet_contDiff family).continuous.norm.continuousOn
  refine ⟨max 1 rawBound, le_max_left _ _, ?_⟩
  intro parameter point pointIn
  have compactIn : (parameter.val, coordinateDirection (planarPart point) (fundamentalTime (point 2))) ∈
      inverseChartCompactDomain family := by
    refine ⟨parameter.property, ⟨(planarPart point, fundamentalTime (point 2)), ?_, rfl⟩⟩
    exact ⟨by simpa [Metric.mem_closedBall, dist_zero_right],
      ⟨(fundamentalTime_mem_Ico (point 2)).1, (fundamentalTime_mem_Ico (point 2)).2.le⟩⟩
  have estimate := rawBoundUpper ⟨_, compactIn, rfl⟩
  change ‖inverseChartJet family
    (parameter.val, coordinateDirection (planarPart point) (fundamentalTime (point 2)))‖ ≤
    rawBound at estimate
  have periodic := periodic_eq_fundamentalTime _
    (inverseChartJet_periodic family parameter.val (planarPart point)) (point 2)
  rw [coordinateDirection_planarPart] at periodic
  rw [← periodic] at estimate
  change max _ _ ≤ rawBound at estimate
  exact ⟨(le_max_left _ _).trans (estimate.trans (le_max_right _ _)),
    (le_max_right _ _).trans (estimate.trans (le_max_right _ _))⟩

end Grad.PhysicalFamily.SampledGlobalEmbedding
