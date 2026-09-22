import SampledSeedInverseChart

noncomputable section

open Set
open scoped ContDiff

namespace Grad.PhysicalFamily.SampledGlobalEmbedding

open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalFamily.IntegerSampling
open Grad.PhysicalFamily.SampledFullGeometry Grad.PhysicalFamily.SampledSmoothFamily
open Grad.MainAssembly.PhysicalNormalHessian Grad.MainAssembly.SampledAxisBasics

def coverNormalLinearMap : Vec →ₗ[ℝ] Vec where
  toFun point := vector (point 0) (point 2) 0
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> simp [vector]
  map_smul' scalar point := by
    ext coordinate
    fin_cases coordinate <;> simp [vector]

def coverNormalCLM : Vec →L[ℝ] Vec := LinearMap.toContinuousLinearMap coverNormalLinearMap

@[simp] theorem coverNormalCLM_apply (point : Vec) :
    coverNormalCLM point = vector (point 0) (point 2) 0 := rfl

def coverRadialCLM : ℝ →L[ℝ] Vec :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (basisVector 0)

@[simp] theorem coverRadialCLM_apply (scalar : ℝ) :
    coverRadialCLM scalar = scalar • basisVector 0 := rfl

theorem coverNormalCLM_norm_le (point : Vec) : ‖coverNormalCLM point‖ ≤ ‖point‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [coverNormalCLM_apply, EuclideanSpace.real_norm_sq_eq, vector, Fin.sum_univ_three]
  positivity

theorem coverRadialCLM_norm (scalar : ℝ) : ‖coverRadialCLM scalar‖ = |scalar| := by
  have basisNorm : ‖basisVector 0‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
    simp [basisVector]
  simp [coverRadialCLM_apply, norm_smul, basisNorm]

theorem physicalToroidalCLM_norm (scalar : ℝ) : ‖physicalToroidalCLM scalar‖ = |scalar| := by
  apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  simp [physicalToroidalCLM_apply, coordinateDirection, vector,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

def cellCoverBaseline (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (parameter : ℝ) (point : Vec) : Vec :=
  coverNormalCLM (cellCoverValue cellLength family 0 parameter point) + physicalToroidalCLM (point 2)

def sampledCoverError (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (parameter : ℝ) (point : Vec) : Vec :=
  coverNormalCLM (cellCoverValue cellLength family (sampledEpsilon period) parameter point -
    cellCoverValue cellLength family 0 parameter point) +
  coverRadialCLM (sampledRadialCorrection cellLength family period parameter point) +
  physicalToroidalCLM (sampledScaledAngle cellLength family period parameter point)

theorem sampledCellCoverMap_eq_baseline_add_error
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (parameter : ℝ) :
    sampledCellCoverMap cellLength family period parameter =
      cellCoverBaseline cellLength family parameter + sampledCoverError cellLength family period parameter := by
  funext point
  ext coordinate
  fin_cases coordinate <;>
    simp [sampledCellCoverMap, cellCoverBaseline, sampledCoverError, coverNormalCLM_apply,
      coverRadialCLM_apply, sampledRadialCorrection, cellCoverValue, sampledScaledAngle,
      physicalToroidalCLM_apply, coordinateDirection, basisVector, vector]
  all_goals ring

theorem cellCoverBaseline_eq_seed (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (parameter : Icc family.lower family.upper) (point : Vec) (pointIn : point ∈ cylinder) :
    cellCoverBaseline cellLength family parameter.val point = seedCoverChart family parameter.val point := by
  rw [cellCoverBaseline, cellCoverValue_zero_eq_seed cellLength family parameter point pointIn]
  ext coordinate
  fin_cases coordinate <;> simp [seedCoverChart, coverNormalCLM_apply, planeEmbedding,
    physicalToroidalCLM_apply, coordinateDirection, vector]

theorem sampledCorrections_differentiableAt
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Icc family.lower family.upper) (point : Vec) (pointIn : point ∈ cylinder)
    (radialPositive : 0 < (period : ℝ) * cellLength +
      cellCoverValue cellLength family (sampledEpsilon period) parameter.val point 0) :
    DifferentiableAt ℝ (sampledScaledAngle cellLength family period parameter.val) point ∧
      DifferentiableAt ℝ (sampledRadialCorrection cellLength family period parameter.val) point := by
  let radial : Vec → ℝ := fun argument => (period : ℝ) * cellLength +
    cellCoverValue cellLength family (sampledEpsilon period) parameter.val argument 0
  let tangential : Vec → ℝ := fun argument =>
    cellCoverValue cellLength family (sampledEpsilon period) parameter.val argument 1
  let radialDerivative := (vecCoordinateCLM 0).comp
    (fderiv ℝ (cellCoverValue cellLength family (sampledEpsilon period) parameter.val) point)
  let tangentialDerivative := (vecCoordinateCLM 1).comp
    (fderiv ℝ (cellCoverValue cellLength family (sampledEpsilon period) parameter.val) point)
  have radialHas : HasFDerivAt radial radialDerivative point := by
    exact ((hasFDerivAt_const (x := point) ((period : ℝ) * cellLength)).add
      (cellCoverCoordinate_hasFDerivAt cellLength family (sampledEpsilon period) epsilonIn
        parameter point pointIn 0)).congr_fderiv (zero_add radialDerivative)
  have tangentialHas : HasFDerivAt tangential tangentialDerivative point :=
    cellCoverCoordinate_hasFDerivAt cellLength family (sampledEpsilon period) epsilonIn
      parameter point pointIn 1
  exact ⟨(cylindricalAngle_hasFDerivAt radial tangential point radialDerivative tangentialDerivative
    radialHas tangentialHas radialPositive period).differentiableAt,
    (cylindricalRadialCorrection_hasFDerivAt radial tangential point radialDerivative tangentialDerivative
      radialHas tangentialHas radialPositive).differentiableAt⟩

theorem cellCoverBaseline_differentiableAt
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (parameter : Icc family.lower family.upper) (point : Vec) (pointIn : point ∈ cylinder) :
    DifferentiableAt ℝ (cellCoverBaseline cellLength family parameter.val) point := by
  have zeroIn : (0 : ℝ) ∈ Ioo (-family.epsilonZero) family.epsilonZero :=
    ⟨neg_neg_iff_pos.mpr family.epsilonPositive, family.epsilonPositive⟩
  have first := coverNormalCLM.differentiableAt.comp point
    (cellCoverValue_differentiableAt cellLength family 0 zeroIn parameter point pointIn)
  have second := physicalToroidalCLM.differentiableAt.comp point (vecCoordinateCLM 2).differentiableAt
  exact first.add second

theorem sampledCoverError_differentiableAt
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Icc family.lower family.upper) (point : Vec) (pointIn : point ∈ cylinder)
    (radialPositive : 0 < (period : ℝ) * cellLength +
      cellCoverValue cellLength family (sampledEpsilon period) parameter.val point 0) :
    DifferentiableAt ℝ (sampledCoverError cellLength family period parameter.val) point := by
  have zeroIn : (0 : ℝ) ∈ Ioo (-family.epsilonZero) family.epsilonZero :=
    ⟨neg_neg_iff_pos.mpr family.epsilonPositive, family.epsilonPositive⟩
  have vDiff := cellCoverValue_differentiableAt cellLength family (sampledEpsilon period)
    epsilonIn parameter point pointIn
  have zeroDiff := cellCoverValue_differentiableAt cellLength family 0 zeroIn parameter point pointIn
  have corrections := sampledCorrections_differentiableAt cellLength family period epsilonIn
    parameter point pointIn radialPositive
  exact ((coverNormalCLM.differentiableAt.comp point (vDiff.sub zeroDiff)).add
    (coverRadialCLM.differentiableAt.comp point corrections.2)).add
      (physicalToroidalCLM.differentiableAt.comp point corrections.1)

theorem sampledCoverError_fderiv
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Icc family.lower family.upper) (point : Vec) (pointIn : point ∈ cylinder)
    (radialPositive : 0 < (period : ℝ) * cellLength +
      cellCoverValue cellLength family (sampledEpsilon period) parameter.val point 0) :
    fderiv ℝ (sampledCoverError cellLength family period parameter.val) point =
      coverNormalCLM.comp
        (fderiv ℝ (cellCoverValue cellLength family (sampledEpsilon period) parameter.val) point -
          fderiv ℝ (cellCoverValue cellLength family 0 parameter.val) point) +
      coverRadialCLM.comp (fderiv ℝ (sampledRadialCorrection cellLength family period parameter.val) point) +
      physicalToroidalCLM.comp (fderiv ℝ (sampledScaledAngle cellLength family period parameter.val) point) := by
  have zeroIn : (0 : ℝ) ∈ Ioo (-family.epsilonZero) family.epsilonZero :=
    ⟨neg_neg_iff_pos.mpr family.epsilonPositive, family.epsilonPositive⟩
  have vDiff := cellCoverValue_differentiableAt cellLength family (sampledEpsilon period)
    epsilonIn parameter point pointIn
  have zeroDiff := cellCoverValue_differentiableAt cellLength family 0 zeroIn parameter point pointIn
  have corrections := sampledCorrections_differentiableAt cellLength family period epsilonIn
    parameter point pointIn radialPositive
  exact (((coverNormalCLM.hasFDerivAt.comp point (vDiff.hasFDerivAt.sub zeroDiff.hasFDerivAt)).add
    (coverRadialCLM.hasFDerivAt.comp point corrections.2.hasFDerivAt)).add
      (physicalToroidalCLM.hasFDerivAt.comp point corrections.1.hasFDerivAt)).fderiv

theorem controlledComponents_norm_le
    (normal : Vec) (radial time : ℝ) :
    ‖coverNormalCLM normal + coverRadialCLM radial + physicalToroidalCLM time‖ ≤
      ‖normal‖ + |radial| + |time| := by
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (coverNormalCLM_norm_le normal)
      (coverRadialCLM_norm radial).le)) (physicalToroidalCLM_norm time).le)

theorem exists_sampledCoverError_bounds
    (cellLength : ℝ) (cellLengthPositive : 0 < cellLength) (family : CellSolutionFamily cellLength) :
    ∃ bound : ℝ, 1 ≤ bound ∧
      ∀ (period : ℕ), 0 < period →
        ∀ (_epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero),
          |sampledEpsilon period| ≤ family.epsilonZero / 2 →
          4 * (family.bound * |sampledEpsilon period|) ≤ 1 → 8 ≤ (period : ℝ) * cellLength →
          ∀ (parameter : Icc family.lower family.upper) (point : Vec), point ∈ cylinder →
            ‖sampledCoverError cellLength family period parameter.val point‖ ≤ bound * |sampledEpsilon period| ∧
            ‖fderiv ℝ (sampledCoverError cellLength family period parameter.val) point‖ ≤
              bound * |sampledEpsilon period| := by
  obtain ⟨perturbationBound, perturbationPositive, perturbationUpper⟩ :=
    exists_cellCoverPerturbation_bounds cellLength family
  obtain ⟨derivativeBound, derivativePositive, correctionUpper⟩ :=
    exists_sampledCylindricalCorrection_bounds cellLength cellLengthPositive family
  let angularConstant := 4 * (2 + 4 * derivativeBound) / cellLength
  let radialConstant := 4 * (2 * derivativeBound + 2)
  let bound := perturbationBound + (radialConstant + angularConstant) * family.bound
  have angularNonnegative : 0 ≤ angularConstant := by dsimp [angularConstant]; positivity
  have radialNonnegative : 0 ≤ radialConstant := by dsimp [radialConstant]; linarith
  have familyBoundNonnegative : 0 ≤ family.bound := le_trans zero_le_one family.boundAtLeastOne
  have boundPositive : 1 ≤ bound := by
    have positive := mul_nonneg (add_nonneg radialNonnegative angularNonnegative) familyBoundNonnegative
    dsimp [bound]
    linarith
  refine ⟨bound, boundPositive, ?_⟩
  intro period periodPositive epsilonIn epsilonSmall errorSmall radiusLarge parameter point pointIn
  have perturbation := perturbationUpper (sampledEpsilon period) epsilonIn epsilonSmall parameter point pointIn
  have corrections := correctionUpper period periodPositive epsilonIn epsilonSmall errorSmall radiusLarge
    parameter point pointIn
  have radialPositive := sampled_major_radial_positive cellLength family period epsilonIn parameter
    (planarPart point) pointIn (point 2) (by nlinarith) (by linarith)
  have totalConstant : perturbationBound * |sampledEpsilon period| +
      radialConstant * (family.bound * |sampledEpsilon period|) +
      angularConstant * (family.bound * |sampledEpsilon period|) = bound * |sampledEpsilon period| := by
    dsimp [bound]
    ring
  constructor
  · exact (controlledComponents_norm_le _ _ _).trans
      ((add_le_add (add_le_add perturbation.1 corrections.2.2.1) corrections.1).trans_eq totalConstant)
  · rw [sampledCoverError_fderiv cellLength family period epsilonIn parameter point pointIn radialPositive]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro direction
    calc
      _ ≤ ‖(fderiv ℝ (cellCoverValue cellLength family (sampledEpsilon period) parameter.val) point -
          fderiv ℝ (cellCoverValue cellLength family 0 parameter.val) point) direction‖ +
        |fderiv ℝ (sampledRadialCorrection cellLength family period parameter.val) point direction| +
        |fderiv ℝ (sampledScaledAngle cellLength family period parameter.val) point direction| :=
          controlledComponents_norm_le _ _ _
      _ ≤ (perturbationBound * |sampledEpsilon period|) * ‖direction‖ +
        (radialConstant * (family.bound * |sampledEpsilon period|)) * ‖direction‖ +
        (angularConstant * (family.bound * |sampledEpsilon period|)) * ‖direction‖ := by
          exact add_le_add (add_le_add
            (((fderiv ℝ (cellCoverValue cellLength family (sampledEpsilon period) parameter.val) point -
              fderiv ℝ (cellCoverValue cellLength family 0 parameter.val) point).le_opNorm direction).trans
                (mul_le_mul_of_nonneg_right perturbation.2 (norm_nonneg _)))
            (((fderiv ℝ (sampledRadialCorrection cellLength family period parameter.val) point).le_opNorm direction).trans
              (mul_le_mul_of_nonneg_right corrections.2.2.2 (norm_nonneg _))))
            (((fderiv ℝ (sampledScaledAngle cellLength family period parameter.val) point).le_opNorm direction).trans
              (mul_le_mul_of_nonneg_right corrections.2.1 (norm_nonneg _)))
      _ = _ := by rw [← add_mul, ← add_mul, totalConstant]

end Grad.PhysicalFamily.SampledGlobalEmbedding
