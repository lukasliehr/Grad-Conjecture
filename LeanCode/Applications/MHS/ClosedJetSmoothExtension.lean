import ClosedJetSmoothRestriction
import FP17Bijection
import P0910Proof

noncomputable section

open Set Filter
open scoped BigOperators ContDiff Topology

namespace Grad.Constraints

open Grad.ClosedJets Grad.CartesianState Grad.DiskExtension.Operator

/-- Constant-in-cell insertion into the accepted ordinary Fourier core. -/
def singletonOrdinaryCore {dimension : ℕ} (field : ClosedJet dimension) :
    OrdinaryCoefficientCore dimension := by
  refine ⟨fun cell => if cell = 0 then field else 0, ?_⟩
  intro grade
  rw [memlp_iff_summable_sq]
  apply ((hasSum_ite_eq (0 : ℤ)
    (‖ordinaryCellGradeRowLinear (grade := grade) 0 field‖ ^ 2)).summable).congr
  intro cell
  by_cases zeroCell : cell = 0 <;>
    simp [ordinaryRawGradeCoordinates, zeroCell]

def constantDiskCellJet {dimension : ℕ} (field : ClosedJet dimension) :
    DiskCellClosedJet dimension := ordinaryReconstructedClosedJet (singletonOrdinaryCore field)

theorem constantDiskCellJet_value {dimension : ℕ} (field : ClosedJet dimension)
    (point : ClosedDisk) (cell : CellCircle) :
    (constantDiskCellJet field).value (point, cell) = field.value point := by
  rw [constantDiskCellJet, ordinaryReconstructedClosedJet_value, ordinaryReconstructedValue_apply]
  rw [tsum_eq_single (0 : ℤ)]
  · simp [singletonOrdinaryCore, cellCharacter]
  · intro other otherNe
    simp [singletonOrdinaryCore, otherNe]

/-- A global extension of one closed jet, obtained from the already accepted
P09 extension at the constant cell mode. No new extension theorem is assumed. -/
def smoothClosedExtension {dimension : ℕ} (field : ClosedJet dimension)
    (point : SpatialPlane) : ComplexEuclidean dimension :=
  ambientExtensionCellLift (constantDiskCellJet field) (assembleSpatialCell point 0)

theorem smoothClosedExtension_smooth {dimension : ℕ} (field : ClosedJet dimension) :
    ContDiff ℝ ∞ (smoothClosedExtension field) := by
  have insertion : ContDiff ℝ ∞ (fun point : SpatialPlane => (point, (0 : ℝ))) :=
    contDiff_id.prodMk contDiff_const
  exact (ambientExtensionCellLift_contDiff_infty (constantDiskCellJet field)).comp
    (assembleSpatialCellCLM.contDiff.comp insertion)

theorem smoothClosedExtension_value {dimension : ℕ} (field : ClosedJet dimension)
    (point : ClosedDisk) : smoothClosedExtension field point.val = field.value point := by
  change ambientExtensionFromValue (constantDiskCellJet field).value
    (planarPart (assembleSpatialCell point.val 0))
      ((assembleSpatialCell point.val 0) 2 : CellCircle) = _
  rw [planarPart_assembleSpatialCell, ambientExtension_inside _ _ point.property]
  exact constantDiskCellJet_value field point _

theorem smoothClosedExtension_restricts {dimension : ℕ} (field : ClosedJet dimension) :
    globalClosedJet (smoothClosedExtension field) (smoothClosedExtension_smooth field) = field :=
  globalClosedJet_eq_of_restriction _ _ field (smoothClosedExtension_value field)

theorem smoothClosedExtension_derivative {dimension order : ℕ} (field : ClosedJet dimension)
    (word : CartesianWord order) (point : ClosedDisk) :
    cartesianDerivative order word (smoothClosedExtension field) point.val =
      closedDerivative field order word point := by
  rw [← globalClosedJet_derivative _ (smoothClosedExtension_smooth field),
    smoothClosedExtension_restricts]

end Grad.Constraints
