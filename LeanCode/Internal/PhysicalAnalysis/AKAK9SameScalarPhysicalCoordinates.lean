import AKAK8LiteralSevenUnknownCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators

/-- Exact scalar multiplication commutes with the literal Fourier series. -/
theorem physicalCharacterSeries_smul (values : (ℤ × ℤ) → ComplexEuclidean 1)
    (scalar : ℂ) (angles : ℝ × ℝ) :
    physicalCharacterSeries (fun mode => scalar • values mode) angles =
      scalar • physicalCharacterSeries values angles := by
  unfold physicalCharacterSeries
  simp only [smul_comm _ scalar,tsum_const_smul'']

/-- Actual coefficient equality identifies the same smooth low row with a
continuous scalar multiple of the original Hilbert reconstruction. -/
theorem fullField_eq_scaledHilbert {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1) (curve : ℕ → ℝ → CellL2 1)
    (continuousCurve : ContinuousOn (curve 0) (Icc lower 1))
    (scalar : ℝ → ℂ) (continuousScalar : ContinuousOn scalar (Icc lower 1))
    (actual : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      lowRhoPhysicalCoefficient parameters lower positive row radius mode = scalar radius • curve 0 radius mode)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    curves.fullField bounded (radius,angles) = scalar radius • hilbertPhysicalField lower bounded curve (radius,angles) := by
  have same (mode : ℤ × ℤ) : curves.physicalCurve 0 radius mode = scalar radius • curve 0 radius mode := by
    apply collarCurve_eq_of_ae lower bounded
      (fun location => curves.physicalCurve 0 location mode)
      (fun location => scalar location • curve 0 location mode)
      ((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode).continuous.comp_continuousOn
        (curves.physicalCurve_smooth bounded 0).continuousOn)
      (continuousScalar.smul ((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode).continuous.comp_continuousOn continuousCurve))
      _ inside
    filter_upwards [curves.physicalCurve_actual bounded 0,actual] with location represented equal
    simpa only [represented mode,pow_zero,one_smul] using equal mode
  rw [fullField_scalarSeries curves bounded radius inside angles]
  rw [funext same,physicalCharacterSeries_smul]
  simp only [hilbertPhysicalField,radialClamp_eq lower bounded.le radius inside]

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

/-- Slot zero is the SAME original x, with no reconstruction choice. -/
theorem fullSeven_physicalX (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (seven.bulkUnit (0 : Fin 1) 0).fullField bounded (radius,angles) =
      originalPhysicalComponentField parameters lower length positive bounded lengthPositive field 0 (radius,angles) := by
  have equality := fullField_eq_scaledHilbert (seven.bulkUnit (0 : Fin 1) 0) bounded
    (originalPhysicalComponentCurve parameters lower length positive bounded lengthPositive field 0)
    (originalPhysicalComponentCurve_smooth parameters lower length positive bounded lengthPositive field allGrades smooth 0 0).continuousOn
    (fun _ => (1 : ℂ)) continuousOn_const
  simp only [one_smul] at equality
  apply equality _ radius inside angles
  filter_upwards [fullStrongSevenInput_firstFour_physical parameters lower length positive bounded lengthPositive data field,
    lowRhoPhysicalCoefficient_bulkUnit parameters lower positive (0 : Fin 1) (0 : Fin 7)
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field)] with location same selected
  intro mode
  rw [selected mode]
  have exactSlot := same mode 0
  simp only [ite_true] at exactSlot
  change _ = (sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive 0 field (radialClamp lower bounded.le location)) mode
  rw [sameCoupledPhysicalXSection_coefficient parameters lower length positive bounded lengthPositive field allGrades]
  exact exactSlot

/-- Slot three is exactly Xi/r for the SAME original Xi. -/
theorem fullSeven_physicalXiOverRadius (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (seven.bulkUnit (0 : Fin 1) 3).fullField bounded (radius,angles) =
      (radius : ℂ)⁻¹ • originalPhysicalComponentField parameters lower length positive bounded lengthPositive field 1 (radius,angles) := by
  apply fullField_eq_scaledHilbert (seven.bulkUnit (0 : Fin 1) 3) bounded
    (originalPhysicalComponentCurve parameters lower length positive bounded lengthPositive field 1)
    (originalPhysicalComponentCurve_smooth parameters lower length positive bounded lengthPositive field allGrades smooth 1 0).continuousOn
    (fun location => (location : ℂ)⁻¹) _ _ radius inside angles
  · exact (Complex.continuous_ofReal.continuousOn).inv₀
      (fun location member => Complex.ofReal_ne_zero.mpr (ne_of_gt (positive.trans_le member.1)))
  · filter_upwards [fullStrongSevenInput_firstFour_physical parameters lower length positive bounded lengthPositive data field,
      lowRhoPhysicalCoefficient_bulkUnit parameters lower positive (0 : Fin 1) (3 : Fin 7)
        (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field)] with location same selected
    intro mode
    rw [selected mode]
    have exactSlot := same mode 3
    simp only [show (3 : Fin 4) ≠ 0 from by decide,show (3 : Fin 4) ≠ 1 from by decide,
      show (3 : Fin 4) ≠ 2 from by decide,if_false] at exactSlot
    change _ = (location : ℂ)⁻¹ • (sameCoupledPhysicalXiSection parameters lower length positive bounded lengthPositive 0 field (radialClamp lower bounded.le location)) mode
    rw [sameCoupledPhysicalXiSection_coefficient parameters lower length positive bounded lengthPositive field allGrades]
    exact exactSlot

end Grad.ActualPolarEquations
