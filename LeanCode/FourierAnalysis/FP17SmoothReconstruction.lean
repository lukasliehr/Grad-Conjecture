import FP17Reconstruction

noncomputable section

set_option maxHeartbeats 500000

open Filter Set
open scoped BigOperators ContDiff Topology

namespace Grad.CartesianState

open Grad.ClosedJets
open Grad.RepresentedKernel.SpatialProduct

local instance fp17SmoothCellPeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩

private def fp17PlanarPartLinear : SpatialCell →ₗ[ℝ] SpatialPlane where
  toFun := planarPart
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> rfl
  map_smul' scalar point := by
    ext coordinate
    fin_cases coordinate <;> rfl

private noncomputable def fp17PlanarPartCLM : SpatialCell →L[ℝ] SpatialPlane :=
  fp17PlanarPartLinear.toContinuousLinearMap

@[simp] private theorem fp17PlanarPartCLM_apply (point : SpatialCell) :
    fp17PlanarPartCLM point = planarPart point := rfl

private noncomputable def fp17CellCoordinateCLM : SpatialCell →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2

@[simp] private theorem fp17CellCoordinateCLM_apply (point : SpatialCell) :
    fp17CellCoordinateCLM point = point 2 := rfl

/-- The real-line representative of the period-`2π` cell character. -/
def cellExponential (cell : ℤ) (coordinate : ℝ) : ℂ :=
  Complex.exp (Complex.I * (cell : ℂ) * (coordinate : ℂ))

theorem cellCharacter_coe (cell : ℤ) (coordinate : ℝ) :
    cellCharacter cell (coordinate : CellCircle) =
      cellExponential cell coordinate := by
  rw [cellCharacter, fourier_coe_apply]
  unfold cellExponential
  congr 1
  have piNonzero : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

@[simp] theorem cellExponential_norm (cell : ℤ) (coordinate : ℝ) :
    ‖cellExponential cell coordinate‖ = 1 := by
  rw [cellExponential, Complex.norm_exp]
  simp

/-- Real Fréchet derivative of one cell exponential. -/
def cellExponentialDerivative (cell : ℤ) (coordinate : ℝ) : ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℂ
      (cellExponential cell coordinate)).restrictScalars ℝ |>.comp
    ((Complex.I * (cell : ℂ)) • Complex.ofRealCLM)

theorem cellExponential_hasFDerivAt (cell : ℤ) (coordinate : ℝ) :
    HasFDerivAt (cellExponential cell)
      (cellExponentialDerivative cell coordinate) coordinate := by
  have inner : HasFDerivAt
      (fun source : ℝ => Complex.I * (cell : ℂ) * (source : ℂ))
      ((Complex.I * (cell : ℂ)) • Complex.ofRealCLM) coordinate := by
    change HasFDerivAt
      (fun source : ℝ =>
        (((Complex.I * (cell : ℂ)) • Complex.ofRealCLM) source))
      ((Complex.I * (cell : ℂ)) • Complex.ofRealCLM) coordinate
    exact ((Complex.I * (cell : ℂ)) • Complex.ofRealCLM).hasFDerivAt
  have outer :=
    (Complex.hasDerivAt_exp
      (Complex.I * (cell : ℂ) * (coordinate : ℂ))).hasFDerivAt.restrictScalars ℝ
  have composed := outer.comp coordinate inner
  change HasFDerivAt
    (Complex.exp ∘ fun source : ℝ =>
      Complex.I * (cell : ℂ) * (source : ℂ))
    (cellExponentialDerivative cell coordinate) coordinate
  simpa only [cellExponentialDerivative, cellExponential] using composed

theorem cellExponential_spatial_fderiv_basis (cell : ℤ)
    (point : SpatialCell) (coordinate : Fin 3) :
    fderiv ℝ (fun candidate : SpatialCell =>
      cellExponential cell (candidate 2)) point
        (spatialCellBasis coordinate) =
      if coordinate = 2 then
        (Complex.I * (cell : ℂ)) * cellExponential cell (point 2)
      else 0 := by
  have composed := (cellExponential_hasFDerivAt cell (point 2)).comp point
    fp17CellCoordinateCLM.hasFDerivAt
  rw [show (fun candidate : SpatialCell => cellExponential cell (candidate 2)) =
      cellExponential cell ∘ fp17CellCoordinateCLM by
    funext candidate
    rfl]
  rw [composed.fderiv]
  fin_cases coordinate <;>
    simp [cellExponentialDerivative, spatialCellBasis,
      fp17CellCoordinateCLM]

def fp17PlanarCoordinate (coordinate : Fin 2) : Fin 3 :=
  ⟨coordinate, coordinate.isLt.trans (by norm_num)⟩

@[simp] private theorem fp17PlanarPartCLM_cellBasis
    (coordinate : Fin 2) :
    fp17PlanarPartCLM (spatialCellBasis (fp17PlanarCoordinate coordinate)) =
      spatialBasis coordinate := by
  ext component
  fin_cases coordinate <;> fin_cases component <;>
    rfl

@[simp] private theorem fp17PlanarPartCLM_cellBasis_two :
    fp17PlanarPartCLM (spatialCellBasis 2) = 0 := by
  ext component
  fin_cases component <;> rfl

/-- The actual ordered planar derivative factor regarded as a function of the
three-dimensional ambient point. -/
def ordinaryPlanarFactor {dimension order : ℕ}
    (field : ClosedJet dimension) (word : CartesianWord order)
    (point : SpatialCell) : ComplexEuclidean dimension :=
  closedPlaneDerivativeEvaluation field
    (fun position => spatialBasis (word position)) (planarPart point)

theorem ordinaryPlanarFactor_contDiffAt {dimension order : ℕ}
    (field : ClosedJet dimension) (word : CartesianWord order)
    (point : SpatialCell) (membership : point ∈ openUnitCylinder) :
    ContDiffAt ℝ ∞ (ordinaryPlanarFactor field word) point := by
  have planarMembership : planarPart point ∈ openUnitDisk := membership
  let evaluation :
      (SpatialPlane [×order]→L[ℝ] ComplexEuclidean dimension) →L[ℝ]
        ComplexEuclidean dimension :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin order => SpatialPlane)
      (ComplexEuclidean dimension)
        (fun position => spatialBasis (word position))
  have planarEvaluationSmooth : ContDiffAt ℝ ∞
      (closedPlaneDerivativeEvaluation field
        (fun position => spatialBasis (word position))) (planarPart point) := by
    change ContDiffAt ℝ ∞
      (evaluation ∘ closedPlaneHigherDerivative field) (planarPart point)
    exact evaluation.contDiff.contDiffAt.comp (planarPart point)
      (closedPlaneHigherDerivative_contDiffAt_interior field
        (planarPart point) planarMembership)
  change ContDiffAt ℝ ∞
    ((closedPlaneDerivativeEvaluation field
      (fun position => spatialBasis (word position))) ∘
        fp17PlanarPartCLM) point
  exact planarEvaluationSmooth.comp point fp17PlanarPartCLM.contDiff.contDiffAt

theorem ordinaryPlanarFactor_fderiv_planarBasis {dimension order : ℕ}
    (field : ClosedJet dimension) (word : CartesianWord order)
    (point : SpatialCell) (membership : point ∈ openUnitCylinder)
    (coordinate : Fin 2) :
    fderiv ℝ (ordinaryPlanarFactor field word) point
        (spatialCellBasis (fp17PlanarCoordinate coordinate)) =
      ordinaryPlanarFactor field (Fin.cons coordinate word) point := by
  have planarMembership : planarPart point ∈ openUnitDisk := membership
  let evaluation :
      (SpatialPlane [×order]→L[ℝ] ComplexEuclidean dimension) →L[ℝ]
        ComplexEuclidean dimension :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin order => SpatialPlane)
      (ComplexEuclidean dimension)
        (fun position => spatialBasis (word position))
  have planarSmooth : ContDiffAt ℝ ∞
      (closedPlaneDerivativeEvaluation field
        (fun position => spatialBasis (word position))) (planarPart point) := by
    change ContDiffAt ℝ ∞
      (evaluation ∘ closedPlaneHigherDerivative field) (planarPart point)
    exact evaluation.contDiff.contDiffAt.comp (planarPart point)
      (closedPlaneHigherDerivative_contDiffAt_interior field
        (planarPart point) planarMembership)
  have composed := (planarSmooth.differentiableAt (by simp)).hasFDerivAt.comp
    point fp17PlanarPartCLM.hasFDerivAt
  change fderiv ℝ
      ((closedPlaneDerivativeEvaluation field
        (fun position => spatialBasis (word position))) ∘ planarPart) point
        (spatialCellBasis (fp17PlanarCoordinate coordinate)) = _
  rw [composed.fderiv, ContinuousLinearMap.comp_apply,
    fp17PlanarPartCLM_cellBasis]
  rw [closedPlaneDerivativeEvaluation_fderiv field _ _ _ planarMembership]
  unfold ordinaryPlanarFactor
  congr 1
  funext position
  exact Fin.cases rfl (fun _ => rfl) position

theorem ordinaryPlanarFactor_fderiv_cellBasis {dimension order : ℕ}
    (field : ClosedJet dimension) (word : CartesianWord order)
    (point : SpatialCell) (membership : point ∈ openUnitCylinder) :
    fderiv ℝ (ordinaryPlanarFactor field word) point
        (spatialCellBasis 2) = 0 := by
  have planarMembership : planarPart point ∈ openUnitDisk := membership
  let evaluation :
      (SpatialPlane [×order]→L[ℝ] ComplexEuclidean dimension) →L[ℝ]
        ComplexEuclidean dimension :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin order => SpatialPlane)
      (ComplexEuclidean dimension)
        (fun position => spatialBasis (word position))
  have planarSmooth : ContDiffAt ℝ ∞
      (closedPlaneDerivativeEvaluation field
        (fun position => spatialBasis (word position))) (planarPart point) := by
    change ContDiffAt ℝ ∞
      (evaluation ∘ closedPlaneHigherDerivative field) (planarPart point)
    exact evaluation.contDiff.contDiffAt.comp (planarPart point)
      (closedPlaneHigherDerivative_contDiffAt_interior field
        (planarPart point) planarMembership)
  have composed := (planarSmooth.differentiableAt (by simp)).hasFDerivAt.comp
    point fp17PlanarPartCLM.hasFDerivAt
  change fderiv ℝ
      ((closedPlaneDerivativeEvaluation field
        (fun position => spatialBasis (word position))) ∘ planarPart) point
        (spatialCellBasis 2) = 0
  rw [composed.fderiv,
    ContinuousLinearMap.comp_apply, fp17PlanarPartCLM_cellBasis_two,
    map_zero]

private noncomputable def fp17ComplexSmul (dimension : ℕ) :
    ℂ →L[ℝ] (ComplexEuclidean dimension) →L[ℝ]
      ComplexEuclidean dimension :=
  (ContinuousLinearMap.lsmul ℂ ℂ :
    ℂ →L[ℂ] (ComplexEuclidean dimension) →L[ℂ]
      ComplexEuclidean dimension).bilinearRestrictScalars ℝ

@[simp] private theorem fp17ComplexSmul_apply {dimension : ℕ}
    (scalar : ℂ) (value : ComplexEuclidean dimension) :
    fp17ComplexSmul dimension scalar value = scalar • value := rfl

private theorem cellExponential_spatial_hasFDerivAt (cell : ℤ)
    (point : SpatialCell) :
    HasFDerivAt (fun candidate : SpatialCell =>
      cellExponential cell (candidate 2))
      ((cellExponentialDerivative cell (point 2)).comp
        fp17CellCoordinateCLM) point := by
  have composed := (cellExponential_hasFDerivAt cell (point 2)).comp point
    fp17CellCoordinateCLM.hasFDerivAt
  change HasFDerivAt
    (cellExponential cell ∘ fp17CellCoordinateCLM)
      ((cellExponentialDerivative cell (point 2)).comp
        fp17CellCoordinateCLM) point
  exact composed

/-- Ambient representative of a fixed mixed derivative Fourier term.  Its
planar factor is the actual ordered derivative tensor supplied by the closed
jet, rather than an independently postulated function. -/
def ordinaryAmbientDerivativeTerm {dimension order : ℕ}
    (word : CartesianWord order) (cellOrder : ℕ) (cell : ℤ)
    (field : ClosedJet dimension) (point : SpatialCell) :
    ComplexEuclidean dimension :=
  cellDerivativeFactor cell cellOrder •
    (cellExponential cell (point 2) •
      closedPlaneDerivativeEvaluation field
        (fun position => spatialBasis (word position)) (planarPart point))

private theorem fp17BilinearDerivative
    {First Second Third : Type*}
    [NormedAddCommGroup First] [NormedSpace ℝ First]
    [NormedAddCommGroup Second] [NormedSpace ℝ Second]
    [NormedAddCommGroup Third] [NormedSpace ℝ Third]
    (bilinearMap : First →L[ℝ] Second →L[ℝ] Third)
    {first : SpatialCell → First} {second : SpatialCell → Second}
    {point : SpatialCell} {firstDerivative : SpatialCell →L[ℝ] First}
    {secondDerivative : SpatialCell →L[ℝ] Second}
    (firstDifferentiable : HasFDerivAt first firstDerivative point)
    (secondDifferentiable : HasFDerivAt second secondDerivative point)
    (direction : SpatialCell) :
    fderiv ℝ (fun source => bilinearMap (first source) (second source))
        point direction =
      bilinearMap (firstDerivative direction) (second point) +
        bilinearMap (first point) (secondDerivative direction) := by
  rw [(bilinearMap.hasFDerivAt_of_bilinear firstDifferentiable
    secondDifferentiable).fderiv]
  simp only [add_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, add_comm]

theorem ordinaryAmbientDerivativeTerm_fderiv_planarBasis
    {dimension order : ℕ} (word : CartesianWord order)
    (cellOrder : ℕ) (cell : ℤ) (field : ClosedJet dimension)
    (point : SpatialCell) (membership : point ∈ openUnitCylinder)
    (coordinate : Fin 2) :
    fderiv ℝ (ordinaryAmbientDerivativeTerm word cellOrder cell field) point
        (spatialCellBasis (fp17PlanarCoordinate coordinate)) =
      ordinaryAmbientDerivativeTerm (Fin.cons coordinate word)
        cellOrder cell field point := by
  let exponential : SpatialCell → ℂ := fun candidate =>
    cellExponential cell (candidate 2)
  let planar : SpatialCell → ComplexEuclidean dimension :=
    ordinaryPlanarFactor field word
  have exponentialHas : HasFDerivAt exponential
      ((cellExponentialDerivative cell (point 2)).comp
        fp17CellCoordinateCLM) point :=
    cellExponential_spatial_hasFDerivAt cell point
  have planarHas : HasFDerivAt planar
      (fderiv ℝ planar point) point :=
    ((ordinaryPlanarFactor_contDiffAt field word point membership).differentiableAt
      (by simp)).hasFDerivAt
  have productHas := (fp17ComplexSmul dimension).hasFDerivAt_of_bilinear
    exponentialHas planarHas
  have scaledHas := productHas.const_smul
    (cellDerivativeFactor cell cellOrder)
  have productDerivative := fp17BilinearDerivative (fp17ComplexSmul dimension)
    exponentialHas planarHas (spatialCellBasis (fp17PlanarCoordinate coordinate))
  have exponentialDerivative :
      ((cellExponentialDerivative cell (point 2)).comp
        fp17CellCoordinateCLM)
          (spatialCellBasis (fp17PlanarCoordinate coordinate)) = 0 := by
    rw [← exponentialHas.fderiv]
    rw [cellExponential_spatial_fderiv_basis]
    exact if_neg (by
      intro equality
      have contradiction := congrArg Fin.val equality
      change coordinate.val = 2 at contradiction
      omega)
  have planarDerivative :
      fderiv ℝ planar point
          (spatialCellBasis (fp17PlanarCoordinate coordinate)) =
        ordinaryPlanarFactor field (Fin.cons coordinate word) point :=
    ordinaryPlanarFactor_fderiv_planarBasis field word point membership coordinate
  change fderiv ℝ
      (cellDerivativeFactor cell cellOrder •
        (fun candidate : SpatialCell =>
          fp17ComplexSmul dimension (exponential candidate)
            (planar candidate))) point
        (spatialCellBasis (fp17PlanarCoordinate coordinate)) = _
  calc
    _ = cellDerivativeFactor cell cellOrder •
        (fderiv ℝ (fun candidate : SpatialCell =>
          fp17ComplexSmul dimension (exponential candidate)
            (planar candidate)) point
          (spatialCellBasis (fp17PlanarCoordinate coordinate))) := by
      rw [scaledHas.fderiv]
      rw [productHas.fderiv]
      rfl
    _ = ordinaryAmbientDerivativeTerm (Fin.cons coordinate word)
        cellOrder cell field point := by
      rw [productDerivative, exponentialDerivative, planarDerivative]
      simp only [fp17ComplexSmul_apply, zero_smul, zero_add]
      rfl

theorem ordinaryAmbientDerivativeTerm_fderiv_cellBasis
    {dimension order : ℕ} (word : CartesianWord order)
    (cellOrder : ℕ) (cell : ℤ) (field : ClosedJet dimension)
    (point : SpatialCell) (membership : point ∈ openUnitCylinder) :
    fderiv ℝ (ordinaryAmbientDerivativeTerm word cellOrder cell field) point
        (spatialCellBasis 2) =
      ordinaryAmbientDerivativeTerm word (cellOrder + 1)
        cell field point := by
  let exponential : SpatialCell → ℂ := fun candidate =>
    cellExponential cell (candidate 2)
  let planar : SpatialCell → ComplexEuclidean dimension :=
    ordinaryPlanarFactor field word
  have exponentialHas : HasFDerivAt exponential
      ((cellExponentialDerivative cell (point 2)).comp
        fp17CellCoordinateCLM) point :=
    cellExponential_spatial_hasFDerivAt cell point
  have planarHas : HasFDerivAt planar
      (fderiv ℝ planar point) point :=
    ((ordinaryPlanarFactor_contDiffAt field word point membership).differentiableAt
      (by simp)).hasFDerivAt
  have productHas := (fp17ComplexSmul dimension).hasFDerivAt_of_bilinear
    exponentialHas planarHas
  have scaledHas := productHas.const_smul
    (cellDerivativeFactor cell cellOrder)
  have productDerivative := fp17BilinearDerivative (fp17ComplexSmul dimension)
    exponentialHas planarHas (spatialCellBasis 2)
  have exponentialDerivative :
      ((cellExponentialDerivative cell (point 2)).comp
        fp17CellCoordinateCLM) (spatialCellBasis 2) =
        (Complex.I * (cell : ℂ)) * cellExponential cell (point 2) := by
    rw [← exponentialHas.fderiv]
    rw [cellExponential_spatial_fderiv_basis, if_pos rfl]
  have planarDerivative :
      fderiv ℝ planar point (spatialCellBasis 2) = 0 :=
    ordinaryPlanarFactor_fderiv_cellBasis field word point membership
  change fderiv ℝ
      (cellDerivativeFactor cell cellOrder •
        (fun candidate : SpatialCell =>
          fp17ComplexSmul dimension (exponential candidate)
            (planar candidate))) point (spatialCellBasis 2) = _
  calc
    _ = cellDerivativeFactor cell cellOrder •
        (fderiv ℝ (fun candidate : SpatialCell =>
          fp17ComplexSmul dimension (exponential candidate)
            (planar candidate)) point (spatialCellBasis 2)) := by
      rw [scaledHas.fderiv, productHas.fderiv]
      rfl
    _ = ordinaryAmbientDerivativeTerm word (cellOrder + 1)
        cell field point := by
      rw [productDerivative, exponentialDerivative, planarDerivative]
      simp only [fp17ComplexSmul_apply, smul_zero, add_zero]
      unfold ordinaryAmbientDerivativeTerm cellDerivativeFactor
      dsimp only [exponential, planar]
      simp only [smul_smul]
      congr 1
      rw [pow_succ]
      ring

private theorem spatialCell_sum_coordinates (point : SpatialCell) :
    (∑ coordinate : Fin 3,
      (point coordinate) • spatialCellBasis coordinate) = point := by
  ext component
  fin_cases component <;>
    simp [Fin.sum_univ_three, spatialCellBasis]

private theorem spatialCellLinear_norm_le_sum_basis
    {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (linear : SpatialCell →L[ℝ] Value) :
    ‖linear‖ ≤ ∑ coordinate : Fin 3,
      ‖linear (spatialCellBasis coordinate)‖ := by
  apply linear.opNorm_le_bound
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro point
  calc
    ‖linear point‖ = ‖linear (∑ coordinate : Fin 3,
        (point coordinate) • spatialCellBasis coordinate)‖ := by
      rw [spatialCell_sum_coordinates]
    _ = ‖∑ coordinate : Fin 3,
        (point coordinate) • linear (spatialCellBasis coordinate)‖ := by
      rw [map_sum]
      apply congrArg norm
      apply Finset.sum_congr rfl
      intro coordinate _
      rw [map_smul]
    _ ≤ ∑ coordinate : Fin 3,
        ‖(point coordinate) • linear (spatialCellBasis coordinate)‖ :=
      norm_sum_le _ _
    _ = ∑ coordinate : Fin 3,
        |point coordinate| * ‖linear (spatialCellBasis coordinate)‖ := by
      apply Finset.sum_congr rfl
      intro coordinate _
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ coordinate : Fin 3,
        ‖point‖ * ‖linear (spatialCellBasis coordinate)‖ := by
      apply Finset.sum_le_sum
      intro coordinate _
      exact mul_le_mul_of_nonneg_right
        (by simpa [Real.norm_eq_abs] using
          PiLp.norm_apply_le point coordinate)
        (norm_nonneg _)
    _ = (∑ coordinate : Fin 3,
        ‖linear (spatialCellBasis coordinate)‖) * ‖point‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro coordinate _
      ring

theorem ordinaryAmbientDerivativeTerm_norm_le
    {dimension order : ℕ} (word : CartesianWord order)
    (cellOrder : ℕ) (cell : ℤ) (field : ClosedJet dimension)
    (point : SpatialCell) (_membership : point ∈ openUnitCylinder) :
    ‖ordinaryAmbientDerivativeTerm word cellOrder cell field point‖ ≤
      |(cell : ℝ)| ^ cellOrder * ‖closedDerivative field order word‖ := by
  unfold ordinaryAmbientDerivativeTerm
  rw [closedPlaneDerivativeEvaluation, closedPlaneHigherDerivative_basis,
    norm_smul, norm_smul, cellDerivativeFactor_norm,
    cellExponential_norm, one_mul]
  exact mul_le_mul_of_nonneg_left
    (ContinuousMap.norm_coe_le_norm _ _)
    (pow_nonneg (abs_nonneg _) _)

/-- The summable three-coordinate majorant for one further ambient
derivative. -/
def ambientFDerivMajorant {dimension order : ℕ}
    (word : CartesianWord order) (cellOrder : ℕ) (cell : ℤ)
    (field : ClosedJet dimension) : ℝ :=
  |(cell : ℝ)| ^ cellOrder *
      ‖closedDerivative field (order + 1) (Fin.cons 0 word)‖ +
    |(cell : ℝ)| ^ cellOrder *
      ‖closedDerivative field (order + 1) (Fin.cons 1 word)‖ +
    |(cell : ℝ)| ^ (cellOrder + 1) *
      ‖closedDerivative field order word‖

theorem ambientFDerivMajorant_summable {dimension order : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ) :
    Summable (fun cell : ℤ => ambientFDerivMajorant word cellOrder cell
      (coefficients.1 cell)) := by
  exact ((physicalDerivative_series_summable coefficients
      (Fin.cons 0 word) cellOrder).add
        (physicalDerivative_series_summable coefficients
          (Fin.cons 1 word) cellOrder)).add
    (physicalDerivative_series_summable coefficients word (cellOrder + 1))

theorem ordinaryAmbientDerivativeTerm_fderiv_norm_le
    {dimension order : ℕ} (word : CartesianWord order)
    (cellOrder : ℕ) (cell : ℤ) (field : ClosedJet dimension)
    (point : SpatialCell) (membership : point ∈ openUnitCylinder) :
    ‖fderiv ℝ (ordinaryAmbientDerivativeTerm word cellOrder cell field) point‖ ≤
      ambientFDerivMajorant word cellOrder cell field := by
  have firstDerivative := ordinaryAmbientDerivativeTerm_fderiv_planarBasis
    word cellOrder cell field point membership (0 : Fin 2)
  have secondDerivative := ordinaryAmbientDerivativeTerm_fderiv_planarBasis
    word cellOrder cell field point membership (1 : Fin 2)
  change fderiv ℝ (ordinaryAmbientDerivativeTerm word cellOrder cell field) point
      (spatialCellBasis 0) =
        ordinaryAmbientDerivativeTerm (Fin.cons 0 word)
          cellOrder cell field point at firstDerivative
  change fderiv ℝ (ordinaryAmbientDerivativeTerm word cellOrder cell field) point
      (spatialCellBasis 1) =
        ordinaryAmbientDerivativeTerm (Fin.cons 1 word)
          cellOrder cell field point at secondDerivative
  calc
    ‖fderiv ℝ (ordinaryAmbientDerivativeTerm word cellOrder cell field) point‖ ≤
        ∑ coordinate : Fin 3,
          ‖fderiv ℝ (ordinaryAmbientDerivativeTerm word cellOrder cell field) point
            (spatialCellBasis coordinate)‖ :=
      spatialCellLinear_norm_le_sum_basis _
    _ = ‖ordinaryAmbientDerivativeTerm (Fin.cons 0 word)
            cellOrder cell field point‖ +
          ‖ordinaryAmbientDerivativeTerm (Fin.cons 1 word)
            cellOrder cell field point‖ +
          ‖ordinaryAmbientDerivativeTerm word (cellOrder + 1)
            cell field point‖ := by
      rw [Fin.sum_univ_three, firstDerivative, secondDerivative,
        ordinaryAmbientDerivativeTerm_fderiv_cellBasis word cellOrder cell field
          point membership]
    _ ≤ ambientFDerivMajorant word cellOrder cell field := by
      unfold ambientFDerivMajorant
      gcongr
      · exact ordinaryAmbientDerivativeTerm_norm_le (Fin.cons 0 word)
          cellOrder cell field point membership
      · exact ordinaryAmbientDerivativeTerm_norm_le (Fin.cons 1 word)
          cellOrder cell field point membership
      · exact ordinaryAmbientDerivativeTerm_norm_le word (cellOrder + 1)
          cell field point membership

private theorem ordinaryAmbientDerivativeTerm_contDiffAt_early
    {dimension order : ℕ} (word : CartesianWord order)
    (cellOrder : ℕ) (cell : ℤ) (field : ClosedJet dimension)
    (point : SpatialCell) (membership : point ∈ openUnitCylinder) :
    ContDiffAt ℝ ∞
      (ordinaryAmbientDerivativeTerm word cellOrder cell field) point := by
  have planarSmooth := ordinaryPlanarFactor_contDiffAt field word point membership
  have realCoordinateSmooth : ContDiffAt ℝ ∞
      (fun candidate : SpatialCell => fp17CellCoordinateCLM candidate) point :=
    fp17CellCoordinateCLM.contDiff.contDiffAt
  have complexCoordinateSmooth : ContDiffAt ℝ ∞
      (fun candidate : SpatialCell =>
        Complex.ofRealCLM (fp17CellCoordinateCLM candidate)) point :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp point realCoordinateSmooth
  have exponentSmooth : ContDiffAt ℝ ∞
      (fun candidate : SpatialCell =>
        Complex.I * (cell : ℂ) *
          Complex.ofRealCLM (fp17CellCoordinateCLM candidate)) point :=
    (contDiffAt_const.mul contDiffAt_const).mul complexCoordinateSmooth
  have exponentialSmooth : ContDiffAt ℝ ∞
      (fun candidate : SpatialCell => cellExponential cell (candidate 2)) point :=
    Complex.contDiff_exp.contDiffAt.comp _ exponentSmooth
  have factorSmooth : ContDiffAt ℝ ∞
      (fun _ : SpatialCell => cellDerivativeFactor cell cellOrder) point :=
    contDiffAt_const
  unfold ordinaryAmbientDerivativeTerm
  exact factorSmooth.smul (exponentialSmooth.smul planarSmooth)

private theorem openUnitCylinder_isPreconnected :
    IsPreconnected openUnitCylinder := by
  have convexCylinder : Convex ℝ openUnitCylinder := by
    have cylinderIdentity :
        openUnitCylinder =
          fp17PlanarPartLinear ⁻¹' Metric.ball (0 : SpatialPlane) 1 := by
      ext point
      change (‖planarPart point‖ < 1) ↔ dist (planarPart point) 0 < 1
      rw [dist_zero_right]
    rw [cylinderIdentity]
    exact (convex_ball (0 : SpatialPlane) 1).linear_preimage
      fp17PlanarPartLinear
  exact convexCylinder.isPreconnected

/-- Ambient sum corresponding to one prescribed planar word and cell order. -/
def ordinaryAmbientDerivativeSeries {dimension order : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ)
    (point : SpatialCell) : ComplexEuclidean dimension :=
  ∑' cell : ℤ,
    ordinaryAmbientDerivativeTerm word cellOrder cell
      (coefficients.1 cell) point

theorem ordinaryAmbientDerivativeSeries_point_summable
    {dimension order : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ)
    (point : SpatialCell) (membership : point ∈ openUnitCylinder) :
    Summable (fun cell : ℤ =>
      ordinaryAmbientDerivativeTerm word cellOrder cell
        (coefficients.1 cell) point) := by
  exact Summable.of_norm_bounded
    (physicalDerivative_series_summable coefficients word cellOrder)
    (fun cell => ordinaryAmbientDerivativeTerm_norm_le word cellOrder cell
      (coefficients.1 cell) point membership)

theorem ordinaryAmbientDerivativeSeries_fderiv_summable
    {dimension order : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ)
    (point : SpatialCell) (membership : point ∈ openUnitCylinder) :
    Summable (fun cell : ℤ =>
      fderiv ℝ (ordinaryAmbientDerivativeTerm word cellOrder cell
        (coefficients.1 cell)) point) := by
  exact Summable.of_norm_bounded
    (ambientFDerivMajorant_summable coefficients word cellOrder)
    (fun cell => ordinaryAmbientDerivativeTerm_fderiv_norm_le word cellOrder cell
      (coefficients.1 cell) point membership)

theorem ordinaryAmbientDerivativeSeries_hasFDerivAt
    {dimension order : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ)
    (point : SpatialCell) (membership : point ∈ openUnitCylinder) :
    HasFDerivAt (ordinaryAmbientDerivativeSeries coefficients word cellOrder)
      (∑' cell : ℤ,
        fderiv ℝ (ordinaryAmbientDerivativeTerm word cellOrder cell
          (coefficients.1 cell)) point) point := by
  let origin : SpatialCell := 0
  have originMembership : origin ∈ openUnitCylinder := by
    change ‖planarPart origin‖ < 1
    rw [show planarPart origin = 0 by
      ext coordinate
      fin_cases coordinate <;> rfl]
    norm_num
  apply hasFDerivAt_tsum_of_isPreconnected
    (ambientFDerivMajorant_summable coefficients word cellOrder)
    openUnitCylinder_isOpen openUnitCylinder_isPreconnected
    (fun cell candidate candidateMembership =>
      ((ordinaryAmbientDerivativeTerm_contDiffAt_early word cellOrder cell
        (coefficients.1 cell) candidate candidateMembership).differentiableAt
          (by simp)).hasFDerivAt)
    (fun cell candidate candidateMembership =>
      ordinaryAmbientDerivativeTerm_fderiv_norm_le word cellOrder cell
        (coefficients.1 cell) candidate candidateMembership)
    originMembership
    (ordinaryAmbientDerivativeSeries_point_summable coefficients word cellOrder
      origin originMembership)
    membership

/-- Differentiating a reconstructed derivative series in either planar
coordinate prepends precisely that coordinate to the ordered planar word. -/
theorem ordinaryAmbientDerivativeSeries_fderiv_planarBasis
    {dimension order : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ)
    (point : SpatialCell) (membership : point ∈ openUnitCylinder)
    (coordinate : Fin 2) :
    fderiv ℝ (ordinaryAmbientDerivativeSeries coefficients word cellOrder) point
        (spatialCellBasis (fp17PlanarCoordinate coordinate)) =
      ordinaryAmbientDerivativeSeries coefficients (Fin.cons coordinate word)
        cellOrder point := by
  have derivativeSummable :=
    ordinaryAmbientDerivativeSeries_fderiv_summable coefficients word cellOrder
      point membership
  rw [(ordinaryAmbientDerivativeSeries_hasFDerivAt coefficients word cellOrder
    point membership).fderiv]
  calc
    (∑' cell : ℤ,
        fderiv ℝ (ordinaryAmbientDerivativeTerm word cellOrder cell
          (coefficients.1 cell)) point)
          (spatialCellBasis (fp17PlanarCoordinate coordinate)) =
        ∑' cell : ℤ,
          fderiv ℝ (ordinaryAmbientDerivativeTerm word cellOrder cell
            (coefficients.1 cell)) point
              (spatialCellBasis (fp17PlanarCoordinate coordinate)) := by
      simpa using (ContinuousLinearMap.apply ℝ
        (ComplexEuclidean dimension)
          (spatialCellBasis (fp17PlanarCoordinate coordinate))).map_tsum
            derivativeSummable
    _ = ordinaryAmbientDerivativeSeries coefficients
        (Fin.cons coordinate word) cellOrder point := by
      apply tsum_congr
      intro cell
      exact ordinaryAmbientDerivativeTerm_fderiv_planarBasis word cellOrder
        cell (coefficients.1 cell) point membership coordinate

/-- Differentiating a reconstructed derivative series in the periodic cell
coordinate raises the cell derivative order by exactly one. -/
theorem ordinaryAmbientDerivativeSeries_fderiv_cellBasis
    {dimension order : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ)
    (point : SpatialCell) (membership : point ∈ openUnitCylinder) :
    fderiv ℝ (ordinaryAmbientDerivativeSeries coefficients word cellOrder) point
        (spatialCellBasis 2) =
      ordinaryAmbientDerivativeSeries coefficients word (cellOrder + 1)
        point := by
  have derivativeSummable :=
    ordinaryAmbientDerivativeSeries_fderiv_summable coefficients word cellOrder
      point membership
  rw [(ordinaryAmbientDerivativeSeries_hasFDerivAt coefficients word cellOrder
    point membership).fderiv]
  calc
    (∑' cell : ℤ,
        fderiv ℝ (ordinaryAmbientDerivativeTerm word cellOrder cell
          (coefficients.1 cell)) point) (spatialCellBasis 2) =
        ∑' cell : ℤ,
          fderiv ℝ (ordinaryAmbientDerivativeTerm word cellOrder cell
            (coefficients.1 cell)) point (spatialCellBasis 2) := by
      simpa using (ContinuousLinearMap.apply ℝ
        (ComplexEuclidean dimension) (spatialCellBasis 2)).map_tsum
          derivativeSummable
    _ = ordinaryAmbientDerivativeSeries coefficients word
        (cellOrder + 1) point := by
      apply tsum_congr
      intro cell
      exact ordinaryAmbientDerivativeTerm_fderiv_cellBasis word cellOrder
        cell (coefficients.1 cell) point membership

private noncomputable def fp17SpatialCoordinateCLM (coordinate : Fin 3) :
    SpatialCell →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 => ℝ) coordinate

@[simp] private theorem fp17SpatialCoordinateCLM_apply
    (coordinate : Fin 3) (point : SpatialCell) :
    fp17SpatialCoordinateCLM coordinate point = point coordinate := rfl

/-- The full Fréchet derivative assembled from the three exact coordinate
series. -/
def ordinaryAmbientDerivativeSeriesCLM
    {dimension order : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ) (point : SpatialCell) :
    SpatialCell →L[ℝ] ComplexEuclidean dimension :=
  (ContinuousLinearMap.smulRightL ℝ SpatialCell
      (ComplexEuclidean dimension)) (fp17SpatialCoordinateCLM 0)
        (ordinaryAmbientDerivativeSeries coefficients (Fin.cons 0 word)
          cellOrder point) +
    (ContinuousLinearMap.smulRightL ℝ SpatialCell
      (ComplexEuclidean dimension)) (fp17SpatialCoordinateCLM 1)
        (ordinaryAmbientDerivativeSeries coefficients (Fin.cons 1 word)
          cellOrder point) +
    (ContinuousLinearMap.smulRightL ℝ SpatialCell
      (ComplexEuclidean dimension)) (fp17SpatialCoordinateCLM 2)
        (ordinaryAmbientDerivativeSeries coefficients word (cellOrder + 1)
          point)

private theorem ordinaryAmbientDerivativeSeries_fderiv_basis_eq_clm
    {dimension order : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ)
    (point : SpatialCell) (membership : point ∈ openUnitCylinder)
    (coordinate : Fin 3) :
    fderiv ℝ (ordinaryAmbientDerivativeSeries coefficients word cellOrder) point
        (spatialCellBasis coordinate) =
      ordinaryAmbientDerivativeSeriesCLM coefficients word cellOrder point
        (spatialCellBasis coordinate) := by
  fin_cases coordinate
  · simpa [ordinaryAmbientDerivativeSeriesCLM, fp17SpatialCoordinateCLM,
      spatialCellBasis, fp17PlanarCoordinate] using
        (ordinaryAmbientDerivativeSeries_fderiv_planarBasis coefficients word
          cellOrder point membership (0 : Fin 2))
  · simpa [ordinaryAmbientDerivativeSeriesCLM, fp17SpatialCoordinateCLM,
      spatialCellBasis, fp17PlanarCoordinate] using
        (ordinaryAmbientDerivativeSeries_fderiv_planarBasis coefficients word
          cellOrder point membership (1 : Fin 2))
  · simpa [ordinaryAmbientDerivativeSeriesCLM, fp17SpatialCoordinateCLM,
      spatialCellBasis] using
        (ordinaryAmbientDerivativeSeries_fderiv_cellBasis coefficients word
          cellOrder point membership)

/-- The actual Fréchet derivative is the finite-coordinate assembly of the
three successor Fourier series. -/
theorem ordinaryAmbientDerivativeSeries_fderiv_eq_clm
    {dimension order : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ)
    (point : SpatialCell) (membership : point ∈ openUnitCylinder) :
    fderiv ℝ (ordinaryAmbientDerivativeSeries coefficients word cellOrder) point =
      ordinaryAmbientDerivativeSeriesCLM coefficients word cellOrder point := by
  apply ContinuousLinearMap.ext
  intro direction
  calc
    fderiv ℝ (ordinaryAmbientDerivativeSeries coefficients word cellOrder) point
        direction =
        fderiv ℝ (ordinaryAmbientDerivativeSeries coefficients word cellOrder)
          point (∑ coordinate : Fin 3,
            (direction coordinate) • spatialCellBasis coordinate) := by
      rw [spatialCell_sum_coordinates]
    _ = ∑ coordinate : Fin 3, (direction coordinate) •
        fderiv ℝ (ordinaryAmbientDerivativeSeries coefficients word cellOrder)
          point (spatialCellBasis coordinate) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro coordinate _
      rw [map_smul]
    _ = ∑ coordinate : Fin 3, (direction coordinate) •
        ordinaryAmbientDerivativeSeriesCLM coefficients word cellOrder point
          (spatialCellBasis coordinate) := by
      apply Finset.sum_congr rfl
      intro coordinate _
      rw [ordinaryAmbientDerivativeSeries_fderiv_basis_eq_clm coefficients word
        cellOrder point membership coordinate]
    _ = ordinaryAmbientDerivativeSeriesCLM coefficients word cellOrder point
        direction := by
      symm
      calc
        ordinaryAmbientDerivativeSeriesCLM coefficients word cellOrder point
            direction =
            ordinaryAmbientDerivativeSeriesCLM coefficients word cellOrder point
              (∑ coordinate : Fin 3,
                (direction coordinate) • spatialCellBasis coordinate) := by
          rw [spatialCell_sum_coordinates]
        _ = ∑ coordinate : Fin 3, (direction coordinate) •
            ordinaryAmbientDerivativeSeriesCLM coefficients word cellOrder point
              (spatialCellBasis coordinate) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro coordinate _
          rw [map_smul]

/-- Every ambient derivative series is smooth to each finite order.  The
induction closes because its full Fréchet derivative is a finite sum of the
three successor series. -/
theorem ordinaryAmbientDerivativeSeries_contDiffOn_nat
    (smoothness : ℕ) {dimension order : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ) :
    ContDiffOn ℝ smoothness
      (ordinaryAmbientDerivativeSeries coefficients word cellOrder)
      openUnitCylinder := by
  induction smoothness generalizing order cellOrder with
  | zero =>
      change ContDiffOn ℝ (0 : WithTop ℕ∞)
        (ordinaryAmbientDerivativeSeries coefficients word cellOrder)
        openUnitCylinder
      rw [contDiffOn_zero]
      intro point membership
      exact (ordinaryAmbientDerivativeSeries_hasFDerivAt coefficients word
        cellOrder point membership).continuousAt.continuousWithinAt
  | succ smoothness inductionHypothesis =>
      rw [show (smoothness.succ : WithTop ℕ∞) =
          (smoothness : WithTop ℕ∞) + 1 by norm_num]
      apply (contDiffOn_succ_iff_fderiv_of_isOpen
        openUnitCylinder_isOpen).2
      refine ⟨?_, ?_, ?_⟩
      · intro point membership
        exact (ordinaryAmbientDerivativeSeries_hasFDerivAt coefficients word
          cellOrder point membership).differentiableAt.differentiableWithinAt
      · intro impossible
        norm_num at impossible
      · have planarZeroSmooth := inductionHypothesis
          (order := order + 1) (word := Fin.cons 0 word)
          (cellOrder := cellOrder)
        have planarOneSmooth := inductionHypothesis
          (order := order + 1) (word := Fin.cons 1 word)
          (cellOrder := cellOrder)
        have cellSmooth := inductionHypothesis
          (order := order) (word := word) (cellOrder := cellOrder + 1)
        have planarZeroCLMSmooth : ContDiffOn ℝ smoothness
            (fun point =>
              (ContinuousLinearMap.smulRightL ℝ SpatialCell
                (ComplexEuclidean dimension)) (fp17SpatialCoordinateCLM 0)
                  (ordinaryAmbientDerivativeSeries coefficients
                    (Fin.cons 0 word) cellOrder point)) openUnitCylinder :=
          ((ContinuousLinearMap.smulRightL ℝ SpatialCell
            (ComplexEuclidean dimension))
              (fp17SpatialCoordinateCLM 0)).contDiff.fun_comp_contDiffOn
                planarZeroSmooth
        have planarOneCLMSmooth : ContDiffOn ℝ smoothness
            (fun point =>
              (ContinuousLinearMap.smulRightL ℝ SpatialCell
                (ComplexEuclidean dimension)) (fp17SpatialCoordinateCLM 1)
                  (ordinaryAmbientDerivativeSeries coefficients
                    (Fin.cons 1 word) cellOrder point)) openUnitCylinder :=
          ((ContinuousLinearMap.smulRightL ℝ SpatialCell
            (ComplexEuclidean dimension))
              (fp17SpatialCoordinateCLM 1)).contDiff.fun_comp_contDiffOn
                planarOneSmooth
        have cellCLMSmooth : ContDiffOn ℝ smoothness
            (fun point =>
              (ContinuousLinearMap.smulRightL ℝ SpatialCell
                (ComplexEuclidean dimension)) (fp17SpatialCoordinateCLM 2)
                  (ordinaryAmbientDerivativeSeries coefficients word
                    (cellOrder + 1) point)) openUnitCylinder :=
          ((ContinuousLinearMap.smulRightL ℝ SpatialCell
            (ComplexEuclidean dimension))
              (fp17SpatialCoordinateCLM 2)).contDiff.fun_comp_contDiffOn
                cellSmooth
        have assembledSmooth : ContDiffOn ℝ smoothness
            (ordinaryAmbientDerivativeSeriesCLM coefficients word cellOrder)
            openUnitCylinder :=
          planarZeroCLMSmooth.add planarOneCLMSmooth |>.add cellCLMSmooth
        exact assembledSmooth.congr (fun point membership =>
          ordinaryAmbientDerivativeSeries_fderiv_eq_clm coefficients word
            cellOrder point membership)

/-- The ambient series is genuinely smooth on the open cylinder. -/
theorem ordinaryAmbientDerivativeSeries_contDiffOn
    {dimension order : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ) :
    ContDiffOn ℝ ∞
      (ordinaryAmbientDerivativeSeries coefficients word cellOrder)
      openUnitCylinder := by
  apply contDiffOn_infty.mpr
  intro smoothness
  exact ordinaryAmbientDerivativeSeries_contDiffOn_nat smoothness coefficients
    word cellOrder

theorem ordinaryAmbientDerivativeTerm_contDiffAt
    {dimension order : ℕ} (word : CartesianWord order)
    (cellOrder : ℕ) (cell : ℤ) (field : ClosedJet dimension)
    (point : SpatialCell) (membership : point ∈ openUnitCylinder) :
    ContDiffAt ℝ ∞
      (ordinaryAmbientDerivativeTerm word cellOrder cell field) point := by
  have planarMembership : planarPart point ∈ openUnitDisk := by
    exact membership
  let evaluation :
      (SpatialPlane [×order]→L[ℝ] ComplexEuclidean dimension) →L[ℝ]
        ComplexEuclidean dimension :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin order => SpatialPlane)
      (ComplexEuclidean dimension)
        (fun position => spatialBasis (word position))
  have planarEvaluationSmooth : ContDiffAt ℝ ∞
      (closedPlaneDerivativeEvaluation field
        (fun position => spatialBasis (word position))) (planarPart point) := by
    change ContDiffAt ℝ ∞
      (evaluation ∘ closedPlaneHigherDerivative field) (planarPart point)
    exact evaluation.contDiff.contDiffAt.comp (planarPart point)
      (closedPlaneHigherDerivative_contDiffAt_interior field
        (planarPart point) planarMembership)
  have planarSmooth : ContDiffAt ℝ ∞
      (fun candidate : SpatialCell =>
        closedPlaneDerivativeEvaluation field
          (fun position => spatialBasis (word position))
            (planarPart candidate)) point := by
    change ContDiffAt ℝ ∞
      ((closedPlaneDerivativeEvaluation field
        (fun position => spatialBasis (word position))) ∘
          fp17PlanarPartCLM) point
    exact planarEvaluationSmooth.comp point fp17PlanarPartCLM.contDiff.contDiffAt
  have exponentialSmooth : ContDiffAt ℝ ∞
      (fun candidate : SpatialCell => cellExponential cell (candidate 2)) point := by
    have realCoordinateSmooth : ContDiffAt ℝ ∞
        (fun candidate : SpatialCell => fp17CellCoordinateCLM candidate) point :=
      fp17CellCoordinateCLM.contDiff.contDiffAt
    have complexCoordinateSmooth : ContDiffAt ℝ ∞
        (fun candidate : SpatialCell =>
          Complex.ofRealCLM (fp17CellCoordinateCLM candidate)) point :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp point realCoordinateSmooth
    have exponentSmooth : ContDiffAt ℝ ∞
        (fun candidate : SpatialCell =>
          Complex.I * (cell : ℂ) *
            Complex.ofRealCLM (fp17CellCoordinateCLM candidate)) point :=
      (contDiffAt_const.mul contDiffAt_const).mul complexCoordinateSmooth
    exact Complex.contDiff_exp.contDiffAt.comp _ exponentSmooth
  have factorSmooth : ContDiffAt ℝ ∞
      (fun _ : SpatialCell => cellDerivativeFactor cell cellOrder) point :=
    contDiffAt_const
  unfold ordinaryAmbientDerivativeTerm
  exact factorSmooth.smul (exponentialSmooth.smul planarSmooth)

theorem ordinaryAmbientDerivativeTerm_eq_diskCellTerm
    {dimension order : ℕ} (word : CartesianWord order)
    (cellOrder : ℕ) (cell : ℤ) (field : ClosedJet dimension)
    (point : SpatialCell) (membership : point ∈ openUnitCylinder) :
    ordinaryAmbientDerivativeTerm word cellOrder cell field point =
      ordinaryDerivativeDiskCellTerm word cellOrder cell field
        (diskCellPoint point
          (openCylinderMembershipClosed point membership)) := by
  rw [ordinaryDerivativeDiskCellTerm_apply]
  unfold ordinaryAmbientDerivativeTerm
  rw [closedPlaneDerivativeEvaluation, closedPlaneHigherDerivative_basis]
  change cellDerivativeFactor cell cellOrder •
      (cellExponential cell (point 2) •
        closedDerivative field order word (ambientClosedDisk (planarPart point))) =
    cellDerivativeFactor cell cellOrder •
      (cellCharacter cell (point 2 : CellCircle) •
        closedDerivative field order word
          ⟨planarPart point, openCylinderMembershipClosed point membership⟩)
  rw [cellCharacter_coe]
  congr 3
  exact Subtype.ext (ambientClosedDisk_val_of_mem
    (openCylinderMembershipClosed point membership))

/-- The lift of every uniform derivative extension is its ambient Fourier
series throughout the open cylinder. -/
theorem diskCellLift_ordinaryDerivativeExtension
    {dimension order : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ)
    (point : SpatialCell) (membership : point ∈ openUnitCylinder) :
    diskCellLift (ordinaryDerivativeExtension coefficients word cellOrder) point =
      ∑' cell : ℤ,
        ordinaryAmbientDerivativeTerm word cellOrder cell
          (coefficients.1 cell) point := by
  rw [diskCellLift, dif_pos (openCylinderMembershipClosed point membership)]
  rw [ordinaryDerivativeExtension_apply]
  apply tsum_congr
  intro cell
  exact (ordinaryAmbientDerivativeTerm_eq_diskCellTerm word cellOrder cell
    (coefficients.1 cell) point membership).symm

end Grad.CartesianState
