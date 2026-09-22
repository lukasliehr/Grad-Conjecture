import AKV11ContinuousOriginalPhysicalRHS

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
namespace Grad.AnnularGeneralSourceRegularity
open Grad.AnnularVariational
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularSourceGraph Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularHighGenerators Grad.AnnularLowEnergy Grad.AnnularHighRadial
open Grad.CircularHighRegularity Grad.AnnularLowClassical

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
include allGrades

theorem originalPairCurve_highX (mode : HighAnnularMode) (radius : ℝ) :
    (originalPairCurve parameters lower length positive bounded lengthPositive field 0 radius).1 mode.val =
      radialSectionExtension 1 lower bounded.le
        (rawHighXSection parameters lower length positive bounded lengthPositive field.ofLp.1.ofLp.2 mode) radius := by
  have same := congrArg Prod.fst
    (originalPairCurve_coefficient parameters lower length positive bounded lengthPositive field allGrades 0 radius mode.val)
  exact same.trans (sameCoupledXCoefficient_high parameters lower length positive bounded lengthPositive field mode _)

theorem originalPairCurve_highXi (mode : HighAnnularMode) (radius : ℝ) :
    (originalPairCurve parameters lower length positive bounded lengthPositive field 0 radius).2 mode.val =
      radialSectionExtension 1 lower bounded.le
        (rawHighXiSection parameters lower length positive bounded field.ofLp.1.ofLp.1 mode) radius := by
  have same := congrArg Prod.snd
    (originalPairCurve_coefficient parameters lower length positive bounded lengthPositive field allGrades 0 radius mode.val)
  exact same.trans (sameCoupledXiCoefficient_high parameters lower length positive bounded lengthPositive field mode _)

theorem originalPairCurve_low (index : LowAnnularIndex) (radius : ℝ) :
    lowPhysicalPairCoefficient index
      (originalPairCurve parameters lower length positive bounded lengthPositive field 0 radius) =
      radialSectionExtension 1 lower bounded.le
        (lowPhysicalSection parameters lower length positive bounded field.ofLp.2 index) radius := by
  rcases index with ⟨entry,mode⟩
  have notLarge : ¬ 3 ≤ |mode.val.1| := by rcases mode.property with h | h <;> omega
  fin_cases entry
  · change sameCoupledPhysicalXiSection parameters lower length positive bounded lengthPositive 0 field
      (radialClamp lower bounded.le radius) mode.val = _
    rw [sameCoupledPhysicalXiSection_coefficient parameters lower length positive bounded lengthPositive field allGrades]
    simp only [sameCoupledXiCoefficient,dif_neg notLarge,dif_pos mode.property,pow_zero,Complex.ofReal_one,one_smul,radialSectionExtension]
    rfl
  · change sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive 0 field
      (radialClamp lower bounded.le radius) mode.val = _
    rw [sameCoupledPhysicalXSection_coefficient parameters lower length positive bounded lengthPositive field allGrades]
    simp only [sameCoupledXCoefficient,dif_neg notLarge,dif_pos mode.property,pow_zero,Complex.ofReal_one,one_smul,radialSectionExtension]
    rfl

theorem originalPairCurve_meanZero (cell : ℤ) (radius : ℝ) :
    hilbertPairCoefficient (0,cell) (originalPairCurve parameters lower length positive bounded lengthPositive field 0 radius) = 0 := by
  rw [originalPairCurve_coefficient parameters lower length positive bounded lengthPositive field allGrades 0 radius (0,cell),
    sameCoupledXCoefficient_meanZero,sameCoupledXiCoefficient_meanZero]
  rfl

end Grad.AnnularGeneralSourceRegularity
