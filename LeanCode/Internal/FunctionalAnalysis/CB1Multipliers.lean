import CB1Scalar

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue Cells FieldL2 fieldCellProjection)
open Grad.CellWeights
open Grad.WeightedJets
open scoped BigOperators

namespace Grad.CellBinomial

theorem fieldGraph_ae (dimension : ℕ) (domain : Set Spatial) (factor : ℤ → ℂ)
    (first second : FieldL2 dimension domain)
    (graph : (first, second) ∈ fieldGraph dimension domain factor) :
    ∀ᵐ point ∂volume.restrict domain, ∀ cell : ℤ,
      second point cell = factor cell • first point cell := by
  apply ae_all_iff.mpr
  intro cell
  have equality := (fieldGraph_mem dimension domain factor first second).mp graph cell
  filter_upwards [Grad.GenericCarriers.fieldCellProjection_ae dimension domain first,
    Grad.GenericCarriers.fieldCellProjection_ae dimension domain second,
    Lp.coeFn_smul (factor cell) (fieldCellProjection dimension domain cell first)]
    with point firstCoordinates secondCoordinates scalar
  rw [← secondCoordinates cell, equality, scalar]
  change factor cell • (fieldCellProjection dimension domain cell first point) = factor cell • first point cell
  rw [firstCoordinates cell]

theorem fieldGraph_of_ae (dimension : ℕ) (domain : Set Spatial) (factor : ℤ → ℂ)
    (first second : FieldL2 dimension domain)
    (coordinates : ∀ᵐ point ∂volume.restrict domain, ∀ cell : ℤ,
      second point cell = factor cell • first point cell) :
    (first, second) ∈ fieldGraph dimension domain factor := by
  apply (fieldGraph_mem dimension domain factor first second).mpr
  intro cell
  apply Lp.ext
  filter_upwards [coordinates,
    Grad.GenericCarriers.fieldCellProjection_ae dimension domain first,
    Grad.GenericCarriers.fieldCellProjection_ae dimension domain second,
    Lp.coeFn_smul (factor cell) (fieldCellProjection dimension domain cell first)]
    with point literal firstCoordinates secondCoordinates scalar
  rw [scalar]
  change fieldCellProjection dimension domain cell second point =
    factor cell • (fieldCellProjection dimension domain cell first point)
  rw [secondCoordinates cell, firstCoordinates cell, literal cell]

theorem fieldGraph_comp (dimension : ℕ) (domain : Set Spatial) (firstFactor secondFactor : ℤ → ℂ)
    {first second third : FieldL2 dimension domain}
    (firstGraph : (first, second) ∈ fieldGraph dimension domain firstFactor)
    (secondGraph : (second, third) ∈ fieldGraph dimension domain secondFactor) :
    (first, third) ∈ fieldGraph dimension domain (fun cell => secondFactor cell * firstFactor cell) := by
  apply (fieldGraph_mem dimension domain _ first third).mpr
  intro cell
  rw [(fieldGraph_mem dimension domain secondFactor second third).mp secondGraph cell,
    (fieldGraph_mem dimension domain firstFactor first second).mp firstGraph cell, smul_smul]

theorem pairing_graph (dimension : ℕ) (domain : Set Spatial) (factor : ℤ → ℂ)
    (first second : FieldL2 dimension domain)
    (graph : (first, second) ∈ fieldGraph dimension domain factor)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : Spatial → ℝ)
    (membership : MemLp test 2 (volume.restrict domain)) :
    Grad.WeakTesting.pairingOfMemLp dimension domain cell vector test membership second =
      factor cell * Grad.WeakTesting.pairingOfMemLp dimension domain cell vector test membership first := by
  rw [Grad.WeakTesting.pairingOfMemLp_apply, Grad.WeakTesting.pairingOfMemLp_apply]
  calc
    _ = ∫ point in domain, factor cell • (test point • inner ℂ vector (first point cell)) := by
      apply integral_congr_ae
      filter_upwards [fieldGraph_ae dimension domain factor first second graph] with point coordinates
      rw [coordinates cell, inner_smul_right]
      exact smul_comm (test point) (factor cell) _
    _ = _ := integral_smul _ _

theorem testPairing_graph (dimension : ℕ) (domain : Set Spatial) (factor : ℤ → ℂ)
    (first second : FieldL2 dimension domain)
    (graph : (first, second) ∈ fieldGraph dimension domain factor)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction domain) :
    testPairing dimension domain cell vector test second =
      factor cell * testPairing dimension domain cell vector test first :=
  pairing_graph dimension domain factor first second graph cell vector test.toFun _

theorem derivativeTestPairing_graph (dimension order : ℕ) (domain : Set Spatial)
    (factor : ℤ → ℂ) (first second : FieldL2 dimension domain)
    (graph : (first, second) ∈ fieldGraph dimension domain factor)
    (index : JetIndex order) (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction domain) :
    derivativeTestPairing dimension order domain index cell vector test second =
      factor cell * derivativeTestPairing dimension order domain index cell vector test first :=
  pairing_graph dimension domain factor first second graph cell vector _ _

section Contraction

variable (Value : Type*) [NormedAddCommGroup Value] [NormedSpace ℂ Value]
  (factor : ℤ → ℂ) (bound : ∀ cell, ‖factor cell‖ ≤ 1)

include bound

theorem contraction_coordinate_norm (cell : ℤ) (value : Value) : ‖factor cell • value‖ ≤ ‖value‖ := by
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_right (bound cell) (norm_nonneg value)).trans_eq (one_mul _)

def contractionCells (cells : Cells Value) : Cells Value :=
  ⟨fun cell => factor cell • cells cell,
    (lp.memℓp cells).mono' (fun cell => contraction_coordinate_norm Value factor bound cell (cells cell))⟩

theorem contractionCells_norm (cells : Cells Value) : ‖contractionCells Value factor bound cells‖ ≤ ‖cells‖ :=
  lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
    (fun cell => contraction_coordinate_norm Value factor bound cell (cells cell))

def contractionCellLinear : Cells Value →ₗ[ℂ] Cells Value where
  toFun := contractionCells Value factor bound
  map_add' first second := lp.ext (funext (fun cell => smul_add (factor cell) (first cell) (second cell)))
  map_smul' scalar cells := lp.ext (funext (fun cell => smul_comm (factor cell) scalar (cells cell)))

def contractionCellCLM : Cells Value →L[ℂ] Cells Value :=
  (contractionCellLinear Value factor bound).mkContinuous 1 (fun cells => by
    change ‖contractionCells Value factor bound cells‖ ≤ 1 * ‖cells‖
    simpa only [one_mul] using contractionCells_norm Value factor bound cells)

theorem contractionCellCLM_apply (cells : Cells Value) (cell : ℤ) :
    contractionCellCLM Value factor bound cells cell = factor cell • cells cell := rfl

theorem contractionCellCLM_norm : ‖contractionCellCLM Value factor bound‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun cells => by
    change ‖contractionCells Value factor bound cells‖ ≤ 1 * ‖cells‖
    simpa only [one_mul] using contractionCells_norm Value factor bound cells)

end Contraction

def contractionFieldCLM (dimension : ℕ) (domain : Set Spatial)
    (factor : ℤ → ℂ) (bound : ∀ cell, ‖factor cell‖ ≤ 1) :
    FieldL2 dimension domain →L[ℂ] FieldL2 dimension domain :=
  (contractionCellCLM (PhysicalValue dimension) factor bound).compLpL 2 (volume.restrict domain)

theorem contractionFieldCLM_norm (dimension : ℕ) (domain : Set Spatial)
    (factor : ℤ → ℂ) (bound : ∀ cell, ‖factor cell‖ ≤ 1) :
    ‖contractionFieldCLM dimension domain factor bound‖ ≤ 1 :=
  (ContinuousLinearMap.norm_compLpL_le (p := 2) (μ := volume.restrict domain)
    (contractionCellCLM (PhysicalValue dimension) factor bound)).trans
      (contractionCellCLM_norm (PhysicalValue dimension) factor bound)

theorem contractionFieldCLM_ae (dimension : ℕ) (domain : Set Spatial)
    (factor : ℤ → ℂ) (bound : ∀ cell, ‖factor cell‖ ≤ 1) (field : FieldL2 dimension domain) :
    ∀ᵐ point ∂volume.restrict domain, ∀ cell : ℤ,
      contractionFieldCLM dimension domain factor bound field point cell = factor cell • field point cell := by
  filter_upwards [(contractionCellCLM (PhysicalValue dimension) factor bound).coeFn_compLpL field]
    with point literal
  intro cell
  exact congrArg (fun cells : Cells (PhysicalValue dimension) => cells cell) literal

theorem contractionFieldCLM_graph (dimension : ℕ) (domain : Set Spatial)
    (factor : ℤ → ℂ) (bound : ∀ cell, ‖factor cell‖ ≤ 1) (field : FieldL2 dimension domain) :
    (field, contractionFieldCLM dimension domain factor bound field) ∈ fieldGraph dimension domain factor :=
  fieldGraph_of_ae dimension domain factor _ _ (contractionFieldCLM_ae dimension domain factor bound field)

theorem contractionFieldCLM_projection (dimension : ℕ) (domain : Set Spatial)
    (factor : ℤ → ℂ) (bound : ∀ cell, ‖factor cell‖ ≤ 1) (field : FieldL2 dimension domain) (cell : ℤ) :
    fieldCellProjection dimension domain cell (contractionFieldCLM dimension domain factor bound field) =
      factor cell • fieldCellProjection dimension domain cell field :=
  (fieldGraph_mem dimension domain factor _ _).mp (contractionFieldCLM_graph dimension domain factor bound field) cell

def operatorJetOfGraph (dimension order : ℕ) (domain : Set Spatial) (factor : ℤ → ℂ)
    (field : FieldL2 dimension domain) (jet : GraphGrade dimension order 0 domain)
    (graph : (field, base dimension order domain (fun _ => 0) jet) ∈ fieldGraph dimension domain factor) :
    OperatorJet dimension order domain factor field where
  inDomain := (fieldOperator_domain dimension domain factor field).mpr
    ⟨base dimension order domain (fun _ => 0) jet, (fieldGraph_mem dimension domain factor _ _).mp graph⟩
  jet := jet
  base_eq := by
    apply fieldGraph_unique dimension domain factor graph
    apply (fieldGraph_mem dimension domain factor _ _).mpr
    intro cell
    exact fieldOperator_apply dimension domain factor _ cell

theorem operatorJetOfGraph_jet (dimension order : ℕ) (domain : Set Spatial) (factor : ℤ → ℂ)
    (field : FieldL2 dimension domain) (jet : GraphGrade dimension order 0 domain)
    (graph : (field, base dimension order domain (fun _ => 0) jet) ∈ fieldGraph dimension domain factor) :
    (operatorJetOfGraph dimension order domain factor field jet graph).jet = jet := rfl

theorem operatorJet_graph (dimension order : ℕ) (domain : Set Spatial) (factor : ℤ → ℂ)
    (field : FieldL2 dimension domain) (witness : OperatorJet dimension order domain factor field) :
    (field, base dimension order domain (fun _ => 0) witness.jet) ∈ fieldGraph dimension domain factor := by
  rw [witness.base_eq]
  apply (fieldGraph_mem dimension domain factor _ _).mpr
  intro cell
  exact fieldOperator_apply dimension domain factor _ cell

theorem operatorJet_jet_unique (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (factor : ℤ → ℂ) (field : FieldL2 dimension domain)
    (first second : OperatorJet dimension order domain factor field) : first.jet = second.jet := by
  apply base_injective dimension order domain openDomain (fun _ => 0)
  rw [first.base_eq, second.base_eq]

end Grad.CellBinomial
