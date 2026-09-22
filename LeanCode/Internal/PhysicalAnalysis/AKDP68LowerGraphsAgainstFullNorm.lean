import AKDP66OriginalLowerGraphAbsorption
import AKDP60SameActualPhaseGraphBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets Grad.NonlinearProduct
open Grad.ActualOriginalSourceMoments Grad.OriginalCartesianTameEstimate Grad.SpatialDilation Grad.CellWeights

private theorem allocatePlanar {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (core : ACore parameters dimension) (epsilon : ℝ) (positive : 0<epsilon) :
    (epsilon/((Fintype.card (JetIndex grade) : ℝ)+1))*originalPlanarNorm parameters grade core≤
      epsilon*originalGradeNorm grade core := by
  let delta := epsilon/((Fintype.card (JetIndex grade) : ℝ)+1)
  have deltaPositive : 0<delta := div_pos positive (by positivity)
  have countBound : delta*(Fintype.card (JetIndex grade) : ℝ)≤epsilon := by
    have exactDelta : delta*((Fintype.card (JetIndex grade) : ℝ)+1)=epsilon := div_mul_cancel₀ epsilon (by positivity)
    nlinarith [deltaPositive]
  have first := mul_le_mul_of_nonneg_left (startupOriginalPlanarNorm_le_full parameters grade core) deltaPositive.le
  have second := mul_le_mul_of_nonneg_right countBound (originalGradeNorm_nonnegative grade core)
  change delta*originalPlanarNorm parameters grade core≤epsilon*originalGradeNorm grade core
  nlinarith only [first,second]

theorem startupOriginalGraph_lower_fullAdjustable (order grade : ℕ) (strict : order<grade)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ constant : ℝ,0≤constant ∧ ∀ (dimension : ℕ) (parameters : PhaseParameters)
      (core : ACore parameters dimension) (graph : GraphGrade dimension order 0 openUnitDisk),
      base dimension order openUnitDisk (fun _ => 0) graph=(originalSourceMoments parameters core).field →
      ‖graph‖≤epsilon*originalGradeNorm grade core+constant*originalCellNorm parameters grade core := by
  obtain ⟨constant,nonnegative,bounded⟩ := startupOriginalGraph_lower_adjustable order grade strict
    (epsilon/((Fintype.card (JetIndex grade) : ℝ)+1)) (div_pos positive (by positivity))
  exact ⟨constant,nonnegative,fun dimension parameters core graph same =>
    (bounded dimension parameters core graph same).trans (add_le_add_left (allocatePlanar parameters grade core epsilon positive) _)⟩

theorem startupActualPhaseFirst_graph_fullAdjustable (parameters : PhaseParameters) (scale : Scale)
    (order grade : ℕ) (allocated : order+1≤grade) (direction : Fin 2) (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ remainder : ℝ,0≤remainder ∧ ∀ (core : ACore parameters 3) (moment : StartupL2 3)
      (output : GraphGrade 3 order 0 openUnitDisk),
      StartupRadialRelated (fun cell _ => cellWeight cell) moment (originalSourceMoments parameters core).field →
      base 3 order openUnitDisk (fun _ => 0) output=
        startupScaledPhaseFirstField parameters.sigma0 parameters.gamma scale.val parameters.gamma_pos.le
          scale.property.1.le scale.property.2 direction moment →
      ‖output‖≤epsilon*originalGradeNorm grade core+remainder*originalCellNorm parameters grade core := by
  obtain ⟨constant,nonnegative,bounded⟩ := startupActualPhaseFirst_graph_bound parameters scale order grade allocated direction
    (epsilon/((Fintype.card (JetIndex grade) : ℝ)+1)) (div_pos positive (by positivity))
  exact ⟨constant,nonnegative,fun core moment output momentSame outputSame =>
    (bounded core moment output momentSame outputSame).trans (add_le_add_left (allocatePlanar parameters grade core epsilon positive) _)⟩

theorem startupActualPhaseSecond_graph_fullAdjustable (parameters : PhaseParameters) (scale : Scale)
    (order grade : ℕ) (allocated : order+2≤grade) (outer inner : Fin 2) (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ remainder : ℝ,0≤remainder ∧ ∀ (core : ACore parameters 3) (moment : StartupL2 3)
      (output : GraphGrade 3 order 0 openUnitDisk),
      StartupRadialRelated (fun cell _ => cellWeight cell^2) moment (originalSourceMoments parameters core).field →
      base 3 order openUnitDisk (fun _ => 0) output=
        startupScaledPhaseSecondField parameters.sigma0 parameters.gamma scale.val parameters.gamma_pos.le
          scale.property.1.le scale.property.2 outer inner moment →
      ‖output‖≤epsilon*originalGradeNorm grade core+remainder*originalCellNorm parameters grade core := by
  obtain ⟨constant,nonnegative,bounded⟩ := startupActualPhaseSecond_graph_bound parameters scale order grade allocated outer inner
    (epsilon/((Fintype.card (JetIndex grade) : ℝ)+1)) (div_pos positive (by positivity))
  exact ⟨constant,nonnegative,fun core moment output momentSame outputSame =>
    (bounded core moment output momentSame outputSame).trans (add_le_add_left (allocatePlanar parameters grade core epsilon positive) _)⟩

end Grad.CartesianStartup
