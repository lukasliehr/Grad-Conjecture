import FC3Core

noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators Topology

namespace Grad.CartesianState

open Grad.ClosedJets

/-- The exact public COR03 boundary: actual disk L² representatives, one all-grade
core, and literal M2 Hilbert coordinates with their fully expanded norm formula. -/
def CoordinateBlockGoal : Prop :=
  (∀ dimension (field : ContinuousMap ClosedDisk (ComplexEuclidean dimension)),
    MemLp (closedDiskLift field) 2 (volume.restrict openUnitDisk)) ∧
  (∀ dimension parameters (coefficients : ℤ → ClosedJet dimension),
    coefficients ∈ originalCoreSubmodule parameters dimension ↔
      ∀ grade : ℕ, Summable (m2CellEnergy parameters grade coefficients)) ∧
  ∀ dimension parameters grade,
    ∃ coordinate : ACore parameters dimension →ₗ[ℂ]
        lp (fun _ : ℤ => CartesianGradeRow dimension grade) 2,
      (∀ coefficients cell (index : GradeMultiIndex grade),
        coordinate coefficients cell index =
          (cellFrequency cell : ℂ) ^ (grade - cartesianOrder index.toCartesian) •
            closedContinuousToDiskL2
              (closedMultiDerivative
                (phaseWeightedJet parameters cell (coefficients.1 cell))
                index.toCartesian)) ∧
      ∀ coefficients,
        ‖coordinate coefficients‖ ^ 2 =
          ∑' cell : ℤ, ∑ index : GradeMultiIndex grade,
            cellFrequency cell ^ (2 * (grade - cartesianOrder index.toCartesian)) *
              ∫ point : SpatialPlane,
                ‖closedDiskLift
                  (closedMultiDerivative
                    (phaseWeightedJet parameters cell (coefficients.1 cell))
                    index.toCartesian) point‖ ^ 2
                  ∂volume.restrict openUnitDisk

end Grad.CartesianState

