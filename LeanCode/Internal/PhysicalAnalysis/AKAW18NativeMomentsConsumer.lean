import AKAW17SameMomentComparison

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.ActualNativeCellMoments
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.ActualPuncturedFamily Grad.AnnularRestriction Grad.AnnularCurrentLow
open Grad.ActualCartesianDescent Grad.CartesianStartup

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow dimension (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second)=rows first)
include compatible

/-- Three genuine joint-cell L2 fields with SAME original-width conjugation
and exact zeroth, first, and second frequency moments. Grade two pays all three. -/
theorem sameNativeCellMoments (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bound : (∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal
      (‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves 2 radius‖ ^ 2)) ≤ ENNReal.ofReal (constant ^ 2)) :
    ∃ field : StartupL2 dimension, ∃ moments : Fin 3 → StartupL2 dimension,
      moments 0 = field ∧
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell,
        field point cell = cartesianWeight parameters cell point •
          gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell point) ∧
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ grade : Fin 3, ∀ cell,
        moments grade point cell = cellFrequency cell ^ grade.val • field point cell) ∧
      (∀ grade : Fin 3, ‖moments grade‖ ≤ Real.sqrt (2 * Real.pi) * constant) := by
  have finite (grade : Fin 3) :
      (∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal
        (‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves grade.val radius‖ ^ 2)) < ⊤ :=
    ((sameConjugatedCurve_grade_energy_le parameters lower positive bounded cofinal decreasing rows curves compatible grade.val 2
      (by omega)).trans bound).trans_lt ENNReal.ofReal_lt_top
  let moments := fun grade : Fin 3 => sameNativeCellField parameters lower positive bounded cofinal decreasing rows curves compatible grade.val (finite grade)
  refine ⟨moments 0,moments,rfl,?_,?_,?_⟩
  · simpa only [moments,Fin.val_zero,pow_zero,one_smul] using
      sameNativeCellField_same parameters lower positive bounded cofinal decreasing rows curves compatible 0 (finite 0)
  · apply ae_all_iff.mpr
    intro grade
    exact sameNativeCellField_moment parameters lower positive bounded cofinal decreasing rows curves compatible grade.val (finite 0) (finite grade)
  · intro grade
    have energy := sameNativeCellField_higherEnergy parameters lower positive bounded cofinal decreasing rows curves compatible
      grade.val 2 (by omega) (finite grade) constant bound
    have realEnergy := ENNReal.toReal_mono (by exact ENNReal.ofReal_ne_top) energy
    have square : ‖moments grade‖ ^ 2 ≤ (2 * Real.pi) * constant ^ 2 := by
      simpa only [ENNReal.toReal_ofReal (sq_nonneg _),ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * Real.pi) * constant ^ 2)] using realEnergy
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) nonnegative)).mp
    rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
    exact square

end Grad.ActualNativeCellMoments
