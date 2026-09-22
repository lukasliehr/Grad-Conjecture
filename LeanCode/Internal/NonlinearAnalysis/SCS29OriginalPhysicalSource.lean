import SCS28DoubleProductCoefficient

noncomputable section
open Set
open scoped BigOperators

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.BoundaryTrace Grad.NonlinearRange Grad.Constraints.Gauges

def corePolarValue {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (angles : ℝ × ℝ) : ComplexEuclidean dimension :=
  Grad.SourceCollar.sourceCoreValue field (polarClosedPoint radius angles.1 nonnegative bounded) angles.2

theorem corePolarValue_continuous {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Continuous (corePolarValue parameters field radius nonnegative bounded) := by
  have pointContinuous : Continuous (fun angles : ℝ × ℝ => polarClosedPoint radius angles.1 nonnegative bounded) :=
    (polarPlane_smooth.continuous.comp (continuous_const.prodMk continuous_fst)).subtype_mk _
  change Continuous (fun angles : ℝ × ℝ => Grad.SourceCollar.sourceCoreValue field
    (polarClosedPoint radius angles.1 nonnegative bounded) angles.2)
  simp_rw [Grad.SourceCollar.sourceCoreValue_eq_originalPhysicalEvaluationLift]
  change Continuous (fun angles : ℝ × ℝ => (originalPhysicalClosedJet parameters field).value
    (polarClosedPoint radius angles.1 nonnegative bounded, (angles.2 : CellCircle)))
  exact (originalPhysicalClosedJet parameters field).value.continuous.comp
    (pointContinuous.prodMk ((AddCircle.continuous_mk' _).comp continuous_snd))

theorem corePolarValue_norm_le {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (angles : ℝ × ℝ) :
    ‖corePolarValue parameters field radius nonnegative bounded angles‖ ≤
      ‖(originalPhysicalClosedJet parameters field).value‖ := by
  rw [corePolarValue, Grad.SourceCollar.sourceCoreValue_eq_originalPhysicalEvaluationLift]
  exact ContinuousMap.norm_coe_le_norm _ _

theorem corePolarValue_axialCoefficient {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (polar : ℝ) (cell : ℤ) :
    angularCoefficient (fun axial => corePolarValue parameters field radius nonnegative bounded (polar, axial)) cell =
      (field.val cell).value (polarClosedPoint radius polar nonnegative bounded) := by
  apply angularCoefficient_of_axialSeries _
    (originalValueNorm_summable parameters field (polarClosedPoint radius polar nonnegative bounded))
  intro axial
  have sum := (coreValue_summable field (polarClosedPoint radius polar nonnegative bounded) axial).hasSum
  apply sum.congr_fun
  intro sourceCell
  congr 1
  exact ((axialPhase_eq_character sourceCell axial).trans (cellCharacter_coe sourceCell axial)).symm

end Grad.SourceCollarFullSource
