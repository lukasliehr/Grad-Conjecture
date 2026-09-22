import AIT99OriginalCoupledInverseConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOriginalLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.PhaseAlgebra Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The original AJ8 value, in the literal unweighted dr ambient. -/
def originalLowValue (lower : ℝ) (index : LowAnnularIndex) :
    LowEnergyAmbient lower →L[ℂ] CollarL2 (ComplexEuclidean 1) lower :=
  lowEnergyCoordinate lower 0 index

/-- The second AJ8 coordinate stores Lambda^-1 v', so the genuine weak
slope is Lambda times that coordinate, at each fixed cell. -/
def originalLowDerivative (lower : ℝ) (index : LowAnnularIndex) :
    LowEnergyAmbient lower →L[ℂ] CollarL2 (ComplexEuclidean 1) lower :=
  (cellFrequency index.2.val.2 : ℂ) • lowEnergyCoordinate lower 1 index

/-- Literal AJ8 Z^0. The value and Lambda^-1 derivative use dr; this graph
is independent of the BE balancing, rho weight, and any coefficient state. -/
def originalLowGraph (lower : ℝ) : Submodule ℂ (LowEnergyAmbient lower) where
  carrier := {field | ∀ index, CollarWeakDerivative lower
    (originalLowValue lower index field) (originalLowDerivative lower index field)}
  zero_mem' := by
    intro index test vector
    simp only [map_zero, neg_zero]
  add_mem' := by
    intro first second firstWeak secondWeak index test vector
    simp only [map_add, firstWeak index test vector, secondWeak index test vector, neg_add]
  smul_mem' := by
    intro scalar field weak index
    simp only [map_smul]
    exact Grad.AnnularReconstruction.collarWeakDerivative_complex_smul lower scalar _ _ (weak index)

theorem originalLowGraph_closed (lower : ℝ) : IsClosed (originalLowGraph lower : Set (LowEnergyAmbient lower)) := by
  change IsClosed {field | ∀ index, ∀ test : CollarTest lower, ∀ vector : ComplexEuclidean 1,
    collarPairing lower test.value vector (originalLowDerivative lower index field) =
      -collarPairing lower test.derivative vector (originalLowValue lower index field)}
  simp only [ofPred_forall]
  exact isClosed_iInter (fun index => isClosed_iInter (fun test => isClosed_iInter (fun vector =>
    isClosed_eq ((collarPairing lower test.value vector).continuous.comp (originalLowDerivative lower index).continuous)
      (((collarPairing lower test.derivative vector).continuous.comp (originalLowValue lower index).continuous).neg))))

instance originalLowGraph_complete (lower : ℝ) : CompleteSpace (originalLowGraph lower) :=
  (originalLowGraph_closed lower).completeSpace_coe

theorem originalLowGraph_norm_sq (lower : ℝ) (field : originalLowGraph lower) :
    ‖field‖ ^ 2 = ‖field.val 0‖ ^ 2 + ‖field.val 1‖ ^ 2 := by
  change ‖field.val‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]

theorem originalLowGraph_mem_iff (lower : ℝ) (field : LowEnergyAmbient lower) :
    field ∈ originalLowGraph lower ↔ ∀ index, CollarWeakDerivative lower (field 0 index)
      (cellFrequency index.2.val.2 • field 1 index) := by
  change (∀ index, CollarWeakDerivative lower (field 0 index) ((cellFrequency index.2.val.2 : ℂ) • field 1 index)) ↔ _
  simp only [Complex.coe_smul]
  rfl

/-- The normalized derivative is uniquely determined by the original value. -/
theorem originalLowGraph_value_injective (lower : ℝ) :
    Function.Injective (fun field : originalLowGraph lower => field.val 0) := by
  intro first second same
  have derivativeSame (index : LowAnnularIndex) :
      originalLowDerivative lower index first.val = originalLowDerivative lower index second.val := by
    apply sub_eq_zero.mp
    apply collarPairing_separates lower
    intro test vector
    rw [map_sub, first.property index test vector, second.property index test vector]
    have valueSame : originalLowValue lower index first.val = originalLowValue lower index second.val :=
      congrArg (fun value : LowEnergyBulk lower => value index) same
    rw [valueSame, sub_self]
  have slopeSame : first.val 1 = second.val 1 := by
    apply lp.ext
    funext index
    have nonzero : (cellFrequency index.2.val.2 : ℂ) ≠ 0 := by
      exact_mod_cast (cellFrequency_pos index.2.val.2).ne'
    apply smul_right_injective (CollarL2 (ComplexEuclidean 1) lower) nonzero
    exact derivativeSame index
  apply Subtype.ext
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · exact same
  · exact slopeSame

end Grad.AnnularOriginalLow
