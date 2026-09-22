import AKAK23SamePhysicalXiAxial

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualCartesianEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (field : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (smooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade) (Icc lower 1))
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field))

include allGrades smooth

/-- Genuine R Xi is radius times the exact normalized slot one of the SAME
original field, before the polar gradient is converted to Cartesian coordinates. -/
theorem fullSeven_physicalXi_angular (radius : ℝ) (inside : radius ∈ Icc lower 1) (polar axial : ℝ) :
    HasDerivAt (fun angle => originalPhysicalComponentField parameters lower length positive bounded lengthPositive field 1 (radius,angle,axial))
      ((radius : ℂ) • (seven.bulkUnit (0 : Fin 1) 1).fullField bounded (radius,polar,axial)) polar := by
  have law := (sharedSeven_classical_angular parameters length lower positive bounded lengthPositive data field seven radius inside polar axial).1
  have nonzero : (radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (positive.trans_le inside.1).ne'
  have same : (fun angle => (radius : ℂ) • (seven.bulkUnit (0 : Fin 1) 3).fullField bounded (radius,angle,axial)) =
      fun angle => originalPhysicalComponentField parameters lower length positive bounded lengthPositive field 1 (radius,angle,axial) := by
    funext angle
    rw [fullSeven_physicalXiOverRadius parameters lower length positive bounded lengthPositive data field allGrades smooth seven radius inside (angle,axial),
      smul_smul,mul_inv_cancel₀ nonzero,one_smul]
  have multiplied := law.const_smul (radius : ℂ)
  change HasDerivAt (fun angle => (radius : ℂ) • (seven.bulkUnit (0 : Fin 1) 3).fullField bounded (radius,angle,axial))
    ((radius : ℂ) • (seven.bulkUnit (0 : Fin 1) 1).fullField bounded (radius,polar,axial)) polar at multiplied
  rw [same] at multiplied
  exact multiplied

end Grad.ActualCartesianEquations
