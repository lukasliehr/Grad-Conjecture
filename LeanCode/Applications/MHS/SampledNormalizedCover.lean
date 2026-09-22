import SampledCoverError

noncomputable section

open Set
open scoped ContDiff

namespace Grad.PhysicalFamily.SampledGlobalEmbedding

open Grad.MainTarget Grad.MainTarget.SemanticBridges Grad.PhysicalFamily
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledFullGeometry
open Grad.PhysicalFamily.SampledSmoothFamily
open Grad.MainAssembly.PhysicalNormalHessian Grad.MainAssembly.SampledAxisBasics

theorem fderiv_eq_of_eqOn_cylinder (first second : Vec → Vec)
    (point : Vec) (pointIn : point ∈ cylinder)
    (firstDifferentiable : DifferentiableAt ℝ first point)
    (secondDifferentiable : DifferentiableAt ℝ second point)
    (equality : EqOn first second cylinder) :
    fderiv ℝ first point = fderiv ℝ second point := by
  have within := fderivWithin_congr' (𝕜 := ℝ) equality pointIn
  rw [fderivWithin_eq_fderiv (uniqueDiffOn_cylinder point pointIn) firstDifferentiable,
    fderivWithin_eq_fderiv (uniqueDiffOn_cylinder point pointIn) secondDifferentiable] at within
  exact within

theorem seedInverseCoverChart_fixed_contDiff (family : CellSolutionFamily cellLength)
    (parameter : ℝ) : ContDiff ℝ ∞ (seedInverseCoverChart family parameter) :=
  (seedInverseCoverChart_contDiff family).comp (f := fun point : Vec => (parameter, point))
    (contDiff_const.prodMk contDiff_id)

theorem seedInverseCoverChart_baseline_fderiv
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (parameter : Icc family.lower family.upper) (point : Vec) (pointIn : point ∈ cylinder) :
    (fderiv ℝ (seedInverseCoverChart family parameter.val)
      (cellCoverBaseline cellLength family parameter.val point)).comp
      (fderiv ℝ (cellCoverBaseline cellLength family parameter.val) point) =
      ContinuousLinearMap.id ℝ Vec := by
  have outer : DifferentiableAt ℝ (seedInverseCoverChart family parameter.val)
      (cellCoverBaseline cellLength family parameter.val point) :=
    ((seedInverseCoverChart_fixed_contDiff family parameter.val).differentiable (by simp)).differentiableAt
  have inner := cellCoverBaseline_differentiableAt cellLength family parameter point pointIn
  have chain := (outer.hasFDerivAt.comp point inner.hasFDerivAt).fderiv
  have identity := fderiv_eq_of_eqOn_cylinder
    (seedInverseCoverChart family parameter.val ∘ cellCoverBaseline cellLength family parameter.val)
    id point pointIn (outer.comp point inner) differentiableAt_id (by
      intro argument argumentIn
      change seedInverseCoverChart family parameter.val
        (cellCoverBaseline cellLength family parameter.val argument) = argument
      rw [cellCoverBaseline_eq_seed cellLength family parameter argument argumentIn,
        seedInverseCoverChart_seedCoverChart])
  rw [identity, fderiv_id] at chain
  exact chain.symm

theorem exists_cellCoverBaseline_fderiv_bound
    (cellLength : ℝ) (family : CellSolutionFamily cellLength) :
    ∃ bound : ℝ, 1 ≤ bound ∧ ∀ (parameter : Icc family.lower family.upper)
      (point : Vec), point ∈ cylinder →
        ‖fderiv ℝ (cellCoverBaseline cellLength family parameter.val) point‖ ≤ bound := by
  obtain ⟨rawBound, rawPositive, rawUpper⟩ := exists_cellCoverValue_fderiv_bound cellLength family
  refine ⟨rawBound + 1, by linarith, ?_⟩
  intro parameter point pointIn
  have zeroIn : (0 : ℝ) ∈ Ioo (-family.epsilonZero) family.epsilonZero :=
    ⟨neg_neg_iff_pos.mpr family.epsilonPositive, family.epsilonPositive⟩
  have rawBoundHere := rawUpper 0 zeroIn (by simpa only [abs_zero] using (half_pos family.epsilonPositive).le)
    (by simp) parameter point pointIn
  have vDiff := cellCoverValue_differentiableAt cellLength family 0 zeroIn parameter point pointIn
  have derivative := ((coverNormalCLM.hasFDerivAt.comp point vDiff.hasFDerivAt).add
    (physicalToroidalCLM.hasFDerivAt.comp point (vecCoordinateCLM 2).hasFDerivAt)).fderiv
  change fderiv ℝ (cellCoverBaseline cellLength family parameter.val) point = _ at derivative
  rw [derivative]
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
  intro direction
  calc
    _ ≤ ‖coverNormalCLM (fderiv ℝ (cellCoverValue cellLength family 0 parameter.val) point direction)‖ +
        ‖physicalToroidalCLM (direction 2)‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ (cellCoverValue cellLength family 0 parameter.val) point direction‖ + |direction 2| :=
      add_le_add (coverNormalCLM_norm_le _) (physicalToroidalCLM_norm _).le
    _ ≤ rawBound * ‖direction‖ + ‖direction‖ :=
      add_le_add (((fderiv ℝ (cellCoverValue cellLength family 0 parameter.val) point).le_opNorm direction).trans
        (mul_le_mul_of_nonneg_right rawBoundHere (norm_nonneg _)))
        (coordinate_abs_le_norm direction 2)
    _ = _ := by ring

theorem cellCoverBaseline_planar_norm_le_two
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (parameter : Icc family.lower family.upper) (point : Vec) (pointIn : point ∈ cylinder) :
    ‖planarPart (cellCoverBaseline cellLength family parameter.val point)‖ ≤ 2 := by
  rw [cellCoverBaseline_eq_seed cellLength family parameter point pointIn,
    seedCoverChart, planarPart_coordinateDirection]
  exact (seedAction_norm_le_two cellLength family parameter.val
    (point 2) (planarPart point) pointIn).le

theorem convex_embeddingTube : Convex ℝ {point : Vec | ‖planarPart point‖ ≤ 6} := by
  have description : {point : Vec | ‖planarPart point‖ ≤ 6} =
      planarLinear ⁻¹' Metric.closedBall 0 6 := by
    ext point
    simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right, mem_ofPred_eq]
    rfl
  rw [description]
  exact (convex_closedBall (0 : Plane) (6 : ℝ)).linear_preimage planarLinear

theorem seedInverseCoverChart_derivative_lipschitz
    (family : CellSolutionFamily cellLength) (bound : ℝ)
    (derivativeBound : ∀ (parameter : Icc family.lower family.upper) (point : Vec), ‖planarPart point‖ ≤ 6 →
      ‖fderiv ℝ (fderiv ℝ (seedInverseCoverChart family parameter.val)) point‖ ≤ bound)
    (parameter : Icc family.lower family.upper) (first second : Vec)
    (firstIn : ‖planarPart first‖ ≤ 6) (secondIn : ‖planarPart second‖ ≤ 6) :
    ‖fderiv ℝ (seedInverseCoverChart family parameter.val) second -
      fderiv ℝ (seedInverseCoverChart family parameter.val) first‖ ≤ bound * ‖second - first‖ := by
  have smooth := (seedInverseCoverChart_fixed_contDiff family parameter.val).fderiv_right
    (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun point _ => (smooth.differentiable (by simp)).differentiableAt)
    (fun point pointIn => derivativeBound parameter point pointIn)
    convex_embeddingTube firstIn secondIn

theorem derivative_comp_error_identity (outer first second : Vec →L[ℝ] Vec)
    (baseOuter : Vec →L[ℝ] Vec)
    (baseIdentity : baseOuter.comp first = ContinuousLinearMap.id ℝ Vec) :
    outer.comp second - ContinuousLinearMap.id ℝ Vec =
      (outer - baseOuter).comp first + outer.comp (second - first) := by
  rw [← baseIdentity]
  ext direction
  simp only [ContinuousLinearMap.comp_apply, sub_apply, add_apply, map_sub]
  abel_nf

theorem norm_comp_le (first second : Vec →L[ℝ] Vec) :
    ‖first.comp second‖ ≤ ‖first‖ * ‖second‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro direction
  exact (first.le_opNorm (second direction)).trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (second.le_opNorm direction) (norm_nonneg first))

theorem exists_sampledNormalizedCellCover_derivative_bound
    (cellLength : ℝ) (cellLengthPositive : 0 < cellLength) (family : CellSolutionFamily cellLength) :
    ∃ bound : ℝ, 1 ≤ bound ∧
      ∀ (period : ℕ), 0 < period →
        ∀ (_epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero),
          |sampledEpsilon period| ≤ family.epsilonZero / 2 →
          4 * (family.bound * |sampledEpsilon period|) ≤ 1 → 8 ≤ (period : ℝ) * cellLength →
          bound * |sampledEpsilon period| ≤ 1 →
          ∀ (parameter : Icc family.lower family.upper) (point : Vec), point ∈ cylinder →
            DifferentiableAt ℝ (sampledNormalizedCellCoverMap cellLength family period parameter.val) point ∧
            ‖fderiv ℝ (sampledNormalizedCellCoverMap cellLength family period parameter.val) point -
              ContinuousLinearMap.id ℝ Vec‖ ≤ bound * |sampledEpsilon period| := by
  obtain ⟨errorBound, errorPositive, errorUpper⟩ := exists_sampledCoverError_bounds cellLength cellLengthPositive family
  obtain ⟨baselineBound, baselinePositive, baselineUpper⟩ := exists_cellCoverBaseline_fderiv_bound cellLength family
  obtain ⟨inverseBound, inversePositive, inverseUpper⟩ := exists_seedInverseCoverChart_bounds family
  let bound := inverseBound * (baselineBound + 1) * errorBound
  have base : 1 ≤ inverseBound * (baselineBound + 1) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ inverseBound - 1)
      (by linarith : 0 ≤ baselineBound)]
  have boundPositive : 1 ≤ bound := by
    simpa only [one_mul] using mul_le_mul base errorPositive (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : 0 ≤ inverseBound * (baselineBound + 1))
  have errorBoundLe : errorBound ≤ bound := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right base (by linarith : 0 ≤ errorBound)
  refine ⟨bound, boundPositive, ?_⟩
  intro period periodPositive epsilonIn epsilonSmall physicalSmall radiusLarge boundSmall parameter point pointIn
  let baseline := cellCoverBaseline cellLength family parameter.val
  let cover := sampledCellCoverMap cellLength family period parameter.val
  let inverse := seedInverseCoverChart family parameter.val
  let error := sampledCoverError cellLength family period parameter.val
  have errorEst := errorUpper period periodPositive epsilonIn epsilonSmall physicalSmall radiusLarge parameter point pointIn
  have errorSmall : ‖error point‖ ≤ 1 := errorEst.1.trans
    ((mul_le_mul_of_nonneg_right errorBoundLe (abs_nonneg _)).trans boundSmall)
  have basePlanar : ‖planarPart (baseline point)‖ ≤ 2 :=
    cellCoverBaseline_planar_norm_le_two cellLength family parameter point pointIn
  have coverIdentity : cover = baseline + error :=
    sampledCellCoverMap_eq_baseline_add_error cellLength family period parameter.val
  have coverPlanar : ‖planarPart (cover point)‖ ≤ 6 := by
    rw [coverIdentity]
    change ‖planarLinear (baseline point + error point)‖ ≤ 6
    rw [map_add]
    have errorPlanar : ‖planarLinear (error point)‖ ≤ 1 :=
      (planarPart_norm_le _).trans errorSmall
    exact (norm_add_le _ _).trans (by change ‖planarPart (baseline point)‖ + ‖planarLinear (error point)‖ ≤ 6; linarith)
  have radialPositive := sampled_major_radial_positive cellLength family period epsilonIn parameter
    (planarPart point) pointIn (point 2) (by nlinarith) (by linarith)
  have baseDiff := cellCoverBaseline_differentiableAt cellLength family parameter point pointIn
  have errorDiff := sampledCoverError_differentiableAt cellLength family period epsilonIn parameter point pointIn radialPositive
  have coverDiff : DifferentiableAt ℝ cover point := by rw [coverIdentity]; exact baseDiff.add errorDiff
  have inverseDiff : DifferentiableAt ℝ inverse (cover point) :=
    ((seedInverseCoverChart_fixed_contDiff family parameter.val).differentiable (by simp)).differentiableAt
  have normalizedIdentity : sampledNormalizedCellCoverMap cellLength family period parameter.val = inverse ∘ cover := rfl
  rw [normalizedIdentity]
  refine ⟨inverseDiff.comp point coverDiff, ?_⟩
  rw [fderiv_comp point inverseDiff coverDiff,
    derivative_comp_error_identity _ (fderiv ℝ baseline point) _ _
      (seedInverseCoverChart_baseline_fderiv cellLength family parameter point pointIn)]
  have derivativeDifference : fderiv ℝ cover point - fderiv ℝ baseline point = fderiv ℝ error point := by
    rw [coverIdentity, fderiv_add baseDiff errorDiff]
    change (fderiv ℝ baseline point + fderiv ℝ error point) - fderiv ℝ baseline point = fderiv ℝ error point
    exact add_sub_cancel_left _ _
  have valueDifference : cover point - baseline point = error point := by rw [coverIdentity]; simp
  have outerDifference := seedInverseCoverChart_derivative_lipschitz family inverseBound
    (fun parameter point pointIn => (inverseUpper parameter point pointIn).2)
    parameter (baseline point) (cover point) (by linarith) coverPlanar
  rw [valueDifference] at outerDifference
  have outerDifferenceBound : ‖fderiv ℝ inverse (cover point) - fderiv ℝ inverse (baseline point)‖ ≤
      inverseBound * (errorBound * |sampledEpsilon period|) :=
    outerDifference.trans (mul_le_mul_of_nonneg_left errorEst.1 (by linarith))
  calc
    _ ≤ ‖(fderiv ℝ inverse (cover point) - fderiv ℝ inverse (baseline point)).comp (fderiv ℝ baseline point)‖ +
        ‖(fderiv ℝ inverse (cover point)).comp (fderiv ℝ cover point - fderiv ℝ baseline point)‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ inverse (cover point) - fderiv ℝ inverse (baseline point)‖ * ‖fderiv ℝ baseline point‖ +
        ‖fderiv ℝ inverse (cover point)‖ * ‖fderiv ℝ cover point - fderiv ℝ baseline point‖ :=
      add_le_add (norm_comp_le _ _) (norm_comp_le _ _)
    _ ≤ (inverseBound * (errorBound * |sampledEpsilon period|)) * baselineBound +
        inverseBound * (errorBound * |sampledEpsilon period|) := by
      rw [derivativeDifference]
      exact add_le_add
        (mul_le_mul outerDifferenceBound (baselineUpper parameter point pointIn) (norm_nonneg _) (by positivity))
        (mul_le_mul (inverseUpper parameter (cover point) coverPlanar).1 errorEst.2 (norm_nonneg _) (by linarith))
    _ = _ := by dsimp [bound]; ring

/-- One finite threshold makes the actual integer-sampled representatives
globally injective on the closed disk times the physical circle. -/
theorem exists_sampledRepresentativeInjectivityThreshold
    (cellLength : ℝ) (cellLengthPositive : 0 < cellLength) (family : CellSolutionFamily cellLength) :
    ∃ firstPeriod : ℕ, 1 ≤ firstPeriod ∧
      ∀ period : ℕ, firstPeriod ≤ period →
        sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero ∧
        ∀ (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
          (potential : ℝ) (parameter : Icc family.lower family.upper),
          Function.Injective (sampledRepresentativeFamily cellLength family period epsilonIn potential parameter).position := by
  obtain ⟨bound, boundPositive, derivativeUpper⟩ :=
    exists_sampledNormalizedCellCover_derivative_bound cellLength cellLengthPositive family
  let margin : ℝ := min (family.epsilonZero / 2) (min (1 / 4) (1 / (2 * bound)))
  have marginPositive : 0 < margin := by
    dsimp [margin]
    exact lt_min (half_pos family.epsilonPositive) (lt_min (by norm_num) (by positivity))
  obtain ⟨firstPeriod, firstPositive, threshold⟩ :=
    Grad.PhysicalFamily.GeometricSamplingThreshold.exists_geometricSamplingThreshold
      cellLength cellLengthPositive family margin marginPositive 8
  refine ⟨firstPeriod, firstPositive, ?_⟩
  intro period periodAfter
  obtain ⟨epsilonMembership, physicalSmall, radiusLarge⟩ := threshold period periodAfter
  refine ⟨epsilonMembership, ?_⟩
  intro epsilonIn potential parameter
  have periodPositive : 0 < period := lt_of_lt_of_le (by omega : 0 < firstPeriod) periodAfter
  have epsilonLePhysical : |sampledEpsilon period| ≤ family.bound * |sampledEpsilon period| := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right family.boundAtLeastOne (abs_nonneg (sampledEpsilon period))
  have epsilonSmall : |sampledEpsilon period| ≤ family.epsilonZero / 2 :=
    epsilonLePhysical.trans (physicalSmall.le.trans (min_le_left _ _))
  have physicalQuarter : family.bound * |sampledEpsilon period| < 1 / 4 :=
    physicalSmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have epsilonBound : |sampledEpsilon period| < 1 / (2 * bound) :=
    epsilonLePhysical.trans_lt (physicalSmall.trans_le
      ((min_le_right _ _).trans (min_le_right _ _)))
  have boundHalf : bound * |sampledEpsilon period| < 1 / 2 := by
    have multiplied := (lt_div_iff₀ (by positivity : 0 < 2 * bound)).mp epsilonBound
    nlinarith
  have pointwise := derivativeUpper period periodPositive epsilonIn epsilonSmall
    (by nlinarith : 4 * (family.bound * |sampledEpsilon period|) ≤ 1) radiusLarge.le
    (by linarith : bound * |sampledEpsilon period| ≤ 1) parameter
  have normalizedInjective := injOn_of_fderiv_close_to_identity
    (sampledNormalizedCellCoverMap cellLength family period parameter.val) cylinder convex_cylinder
    (1 / 2) (by norm_num) (fun point pointIn => (pointwise point pointIn).1)
    (fun point pointIn => ((pointwise point pointIn).2).trans boundHalf.le)
  have coverInjective := sampledCellCover_injective_of_normalized_injective cellLength family period
    parameter.val normalizedInjective
  exact sampledRepresentative_position_injective_of_cellCover cellLength family period periodPositive
    epsilonIn potential parameter (by linarith) (by linarith) coverInjective

end Grad.PhysicalFamily.SampledGlobalEmbedding
