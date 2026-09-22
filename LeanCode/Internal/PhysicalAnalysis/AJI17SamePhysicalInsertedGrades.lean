import AJI16SameCoupledFourierFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularJointRegularity Grad.AnnularLowEnergy Grad.AnnularOmegaGraph Grad.AnnularFluxTrace
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularHighTilt Grad.AnnularTiltedReference
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive)

theorem sameCoupledXiCoefficient_grade (grade : ℕ) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field grade radius mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0 radius mode := by
  unfold sameCoupledXiCoefficient
  split_ifs <;> simp only [pow_zero, Complex.ofReal_one, one_smul, smul_zero]
  exact smul_comm _ _ _

theorem sameCoupledXiCoefficient_meanZero (grade : ℕ) (radius : Icc lower (1 : ℝ)) (cell : ℤ) :
    sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field grade radius (0, cell) = 0 := by
  norm_num [sameCoupledXiCoefficient]

theorem sameCoupledXCoefficient_grade (grade : ℕ) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field grade radius mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0 radius mode := by
  unfold sameCoupledXCoefficient
  split_ifs <;> simp only [pow_zero, Complex.ofReal_one, one_smul, smul_zero]
  exact smul_comm _ _ _

theorem sameCoupledXCoefficient_meanZero (grade : ℕ) (radius : Icc lower (1 : ℝ)) (cell : ℤ) :
    sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field grade radius (0, cell) = 0 := by
  norm_num [sameCoupledXCoefficient]

variable (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
include allGrades

theorem sameCoupledPhysicalXiSection_grade (grade : ℕ) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    sameCoupledPhysicalXiSection parameters lower length positive bounded lengthPositive grade field radius mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        sameCoupledPhysicalXiSection parameters lower length positive bounded lengthPositive 0 field radius mode := by
  rw [sameCoupledPhysicalXiSection_coefficient parameters lower length positive bounded lengthPositive field allGrades,
    sameCoupledPhysicalXiSection_coefficient parameters lower length positive bounded lengthPositive field allGrades]
  exact sameCoupledXiCoefficient_grade parameters lower length positive bounded lengthPositive field grade radius mode

theorem sameCoupledPhysicalXiSection_meanZero (grade : ℕ) (radius : Icc lower (1 : ℝ)) (cell : ℤ) :
    sameCoupledPhysicalXiSection parameters lower length positive bounded lengthPositive grade field radius (0, cell) = 0 := by
  rw [sameCoupledPhysicalXiSection_coefficient parameters lower length positive bounded lengthPositive field allGrades]
  exact sameCoupledXiCoefficient_meanZero parameters lower length positive bounded lengthPositive field grade radius cell

theorem sameCoupledPhysicalXSection_grade (grade : ℕ) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive grade field radius mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive 0 field radius mode := by
  rw [sameCoupledPhysicalXSection_coefficient parameters lower length positive bounded lengthPositive field allGrades,
    sameCoupledPhysicalXSection_coefficient parameters lower length positive bounded lengthPositive field allGrades]
  exact sameCoupledXCoefficient_grade parameters lower length positive bounded lengthPositive field grade radius mode

theorem sameCoupledPhysicalXSection_meanZero (grade : ℕ) (radius : Icc lower (1 : ℝ)) (cell : ℤ) :
    sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive grade field radius (0, cell) = 0 := by
  rw [sameCoupledPhysicalXSection_coefficient parameters lower length positive bounded lengthPositive field allGrades]
  exact sameCoupledXCoefficient_meanZero parameters lower length positive bounded lengthPositive field grade radius cell

end Grad.AnnularSmoothCore
