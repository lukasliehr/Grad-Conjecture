import AKCX35ActualPhaseSecondGraphSymbol

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets Grad.CellWeights

/-- Exact first phase field, on the SAME supplied natural moment. -/
theorem startupScaledPhaseFirstField_spatialGraph (sigma gamma scale : ℝ)
    (nonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale) (scaleOne : scale ≤ 1)
    (order : ℕ) (direction : Fin 2) (field moment : StartupL2 3)
    (regular : ∃ graph : GraphGrade 3 order (order+1) openUnitDisk,
      base 3 order openUnitDisk (fun _ => order+1) graph = field)
    (sameMoment : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      moment point cell = cellWeight cell • field point cell) :
    ∃ graph : GraphGrade 3 order 0 openUnitDisk,
      base 3 order openUnitDisk (fun _ => 0) graph =
        startupScaledPhaseFirstField sigma gamma scale nonnegative scaleNonnegative scaleOne direction moment := by
  obtain ⟨input,sameInput⟩ := regular
  apply (startupPhaseSlopeSymbol sigma gamma scale nonnegative scaleNonnegative order direction).graph_exists input
  rw [sameInput]
  simpa only [startupPhaseSlopeSymbol,Complex.coe_smul] using
    startupScaledPhaseFirstField_same sigma gamma scale nonnegative scaleNonnegative scaleOne direction field moment sameMoment

/-- Exact second phase field, including the genuine Hessian and gradient square. -/
theorem startupScaledPhaseSecondField_spatialGraph (sigma gamma scale : ℝ)
    (nonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale) (scaleOne : scale ≤ 1)
    (order : ℕ) (outer inner : Fin 2) (field moment : StartupL2 3)
    (regular : ∃ graph : GraphGrade 3 order (order+2) openUnitDisk,
      base 3 order openUnitDisk (fun _ => order+2) graph = field)
    (sameMoment : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      moment point cell = cellWeight cell ^ 2 • field point cell) :
    ∃ graph : GraphGrade 3 order 0 openUnitDisk,
      base 3 order openUnitDisk (fun _ => 0) graph =
        startupScaledPhaseSecondField sigma gamma scale nonnegative scaleNonnegative scaleOne outer inner moment := by
  obtain ⟨input,sameInput⟩ := regular
  apply (startupPhaseSecondSymbol sigma gamma scale nonnegative scaleNonnegative order outer inner).graph_exists input
  rw [sameInput]
  simpa only [startupPhaseSecondSymbol,Complex.coe_smul] using
    startupScaledPhaseSecondField_same sigma gamma scale nonnegative scaleNonnegative scaleOne outer inner field moment sameMoment

end Grad.CartesianStartup
