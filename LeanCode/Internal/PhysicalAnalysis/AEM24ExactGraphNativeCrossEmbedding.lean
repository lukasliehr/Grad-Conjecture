import AEM23CompleteCrossDataMaps
import AEK16ExactBaseBF13Consumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.ActualBoundaryPrimitives Grad.AnnularCurrentSource Grad.GaugeCoefficients.Physical.Allocation

/-- Exact BF16 source subset in AEK's original weighted order (F0,RF0,F2,f). -/
def crossKnownWeighted (parameters : PhaseParameters) (lower : ℝ) (data : CrossHighData parameters lower) :
    HighKnownSourceBulk lower :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 4 => DivisionRow 1 lower)).symm
    ![0, 0, 0, highBulkIntoFull lower (data.ofLp.1 0)]

def crossKnownAuxiliary (parameters : PhaseParameters) (lower : ℝ) (data : CrossHighData parameters lower) :
    HighAuxiliarySourceBulk lower :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => DivisionRow 1 lower)).symm
    ![0, highBulkIntoFull lower (data.ofLp.1 1), highBulkIntoFull lower (data.ofLp.1 2)]

theorem crossKnownWeighted_graph (parameters : PhaseParameters) (lower : ℝ) (data : CrossHighData parameters lower) :
    WeightedGraphCompatibility parameters lower 0 (0 : HighRadialSourceGraphs parameters lower 0)
      (crossKnownWeighted parameters lower data) := by
  unfold WeightedGraphCompatibility
  simp only [Prod.fst_zero, Prod.snd_zero, map_zero]
  filter_upwards [Lp.coeFn_zero (ComplexEuclidean 1) 2 (volume.restrict (Icc lower 1))] with radius zero
  intro mode
  change (0 : RadialL2 1 lower) radius = ((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ) • (0 : RadialL2 1 lower) radius ∧
    (0 : RadialL2 1 lower) radius = ((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ) • (0 : RadialL2 1 lower) radius ∧
    (0 : RadialL2 1 lower) radius = ((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ) • (0 : RadialL2 1 lower) radius
  simp only [zero, Pi.zero_apply, smul_zero, and_self]

/-- The original source-native known datum, with zero actual source graphs,
zero g and zero inner value. This is the genuine fixed BF16 subspace. -/
def CrossHighData.toGraphKnown (parameters : PhaseParameters) (lower : ℝ) (data : CrossHighData parameters lower) :
    ActualHighGraphKnownData parameters lower 0 0 where
  weighted := crossKnownWeighted parameters lower data
  auxiliary := crossKnownAuxiliary parameters lower data
  graphs := 0
  datum := data.ofLp.2
  innerValue := 0
  weightedGraph := crossKnownWeighted_graph parameters lower data

theorem crossKnown_exact_slots (parameters : PhaseParameters) (lower : ℝ) (data : CrossHighData parameters lower) :
    (data.toGraphKnown parameters lower).weighted 0 = 0 ∧
    (data.toGraphKnown parameters lower).weighted 1 = 0 ∧
    (data.toGraphKnown parameters lower).weighted 2 = 0 ∧
    (data.toGraphKnown parameters lower).weighted 3 = highBulkIntoFull lower (data.ofLp.1 0) ∧
    (data.toGraphKnown parameters lower).auxiliary 0 = 0 ∧
    (data.toGraphKnown parameters lower).auxiliary 1 = highBulkIntoFull lower (data.ofLp.1 1) ∧
    (data.toGraphKnown parameters lower).auxiliary 2 = highBulkIntoFull lower (data.ofLp.1 2) ∧
    (data.toGraphKnown parameters lower).graphs = 0 ∧
    (data.toGraphKnown parameters lower).datum = data.ofLp.2 ∧
    (data.toGraphKnown parameters lower).innerValue = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem crossKnownWeighted_add (parameters : PhaseParameters) (lower : ℝ) (first second : CrossHighData parameters lower) :
    crossKnownWeighted parameters lower (first + second) = crossKnownWeighted parameters lower first + crossKnownWeighted parameters lower second := by
  apply PiLp.ext
  intro slot
  fin_cases slot <;> simp [crossKnownWeighted, map_add]

theorem crossKnownWeighted_smul (parameters : PhaseParameters) (lower : ℝ) (scalar : ℂ) (data : CrossHighData parameters lower) :
    crossKnownWeighted parameters lower (scalar • data) = scalar • crossKnownWeighted parameters lower data := by
  apply PiLp.ext
  intro slot
  fin_cases slot <;> simp [crossKnownWeighted, map_smul]

theorem crossKnownAuxiliary_add (parameters : PhaseParameters) (lower : ℝ) (first second : CrossHighData parameters lower) :
    crossKnownAuxiliary parameters lower (first + second) = crossKnownAuxiliary parameters lower first + crossKnownAuxiliary parameters lower second := by
  apply PiLp.ext
  intro slot
  fin_cases slot <;> simp [crossKnownAuxiliary, map_add]

theorem crossKnownAuxiliary_smul (parameters : PhaseParameters) (lower : ℝ) (scalar : ℂ) (data : CrossHighData parameters lower) :
    crossKnownAuxiliary parameters lower (scalar • data) = scalar • crossKnownAuxiliary parameters lower data := by
  apply PiLp.ext
  intro slot
  fin_cases slot <;> simp [crossKnownAuxiliary, map_smul]


/-- The fixed source-subset embedding preserves the complete Hilbert norm. -/
theorem crossKnown_embedding_norm_sq (parameters : PhaseParameters) (lower : ℝ) (data : CrossHighData parameters lower) :
    ‖crossKnownWeighted parameters lower data‖ ^ 2 + ‖crossKnownAuxiliary parameters lower data‖ ^ 2 +
      ‖(data.toGraphKnown parameters lower).datum‖ ^ 2 = ‖data‖ ^ 2 := by
  have weighted : ‖crossKnownWeighted parameters lower data‖ ^ 2 = ‖data.ofLp.1 0‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    change (∑ slot : Fin 4, ‖(![0, 0, 0, highBulkIntoFull lower (data.ofLp.1 0)] slot : DivisionRow 1 lower)‖ ^ 2) = _
    simp [Fin.sum_univ_succ, (highBulkIntoFull lower).norm_map]
  have auxiliary : ‖crossKnownAuxiliary parameters lower data‖ ^ 2 = ‖data.ofLp.1 1‖ ^ 2 + ‖data.ofLp.1 2‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    change (∑ slot : Fin 3, ‖(![0, highBulkIntoFull lower (data.ofLp.1 1), highBulkIntoFull lower (data.ofLp.1 2)] slot : DivisionRow 1 lower)‖ ^ 2) = _
    simp [Fin.sum_univ_succ, (highBulkIntoFull lower).norm_map]
  have bulk := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => AnnularBulk lower) data.ofLp.1
  rw [Fin.sum_univ_three] at bulk
  have pair := WithLp.prod_norm_sq_eq_of_L2 data
  change ‖data‖ ^ 2 = ‖data.ofLp.1‖ ^ 2 + ‖data.ofLp.2‖ ^ 2 at pair
  change ‖crossKnownWeighted parameters lower data‖ ^ 2 + ‖crossKnownAuxiliary parameters lower data‖ ^ 2 + ‖data.ofLp.2‖ ^ 2 = _
  linarith

theorem crossKnown_embedding_bounds (parameters : PhaseParameters) (lower : ℝ) (data : CrossHighData parameters lower) :
    ‖(data.toGraphKnown parameters lower).weighted‖ ≤ ‖data‖ ∧
    ‖(data.toGraphKnown parameters lower).auxiliary‖ ≤ ‖data‖ ∧
    ‖(data.toGraphKnown parameters lower).datum‖ ≤ ‖data‖ := by
  have square := crossKnown_embedding_norm_sq parameters lower data
  change ‖crossKnownWeighted parameters lower data‖ ≤ ‖data‖ ∧
    ‖crossKnownAuxiliary parameters lower data‖ ≤ ‖data‖ ∧ ‖data.ofLp.2‖ ≤ ‖data‖
  change ‖crossKnownWeighted parameters lower data‖ ^ 2 + ‖crossKnownAuxiliary parameters lower data‖ ^ 2 + ‖data.ofLp.2‖ ^ 2 = _ at square
  have first := sq_nonneg ‖crossKnownWeighted parameters lower data‖
  have second := sq_nonneg ‖crossKnownAuxiliary parameters lower data‖
  have third := sq_nonneg ‖data.ofLp.2‖
  constructor
  · nlinarith [norm_nonneg (crossKnownWeighted parameters lower data), norm_nonneg data]
  constructor
  · nlinarith [norm_nonneg (crossKnownAuxiliary parameters lower data), norm_nonneg data]
  · nlinarith [norm_nonneg data.ofLp.2, norm_nonneg data]

end Grad.AnnularCrossMaps
