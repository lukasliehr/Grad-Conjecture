import AKCX1SameAllPowerWeightedFirst
import AKCX4ActualSpatialRemainderFirst

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets Grad.CellWeights Grad.CellBinomial
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

/-- One completed spatial induction grade, simultaneously at every signed
axial power and every natural input cell reserve. -/
def StartupSignedFamily.HasSpatialGrade {dimension : ℕ} {L ell : ℝ}
    (family : StartupSignedFamily dimension L ell) (order : ℕ) : Prop :=
  ∀ power weight : ℕ, ∃ graph : GraphGrade dimension order weight openUnitDisk,
    base dimension order openUnitDisk (fun _ => weight) graph = family.moment power

namespace StartupSignedFamily
variable {dimension input output order : ℕ} {L ell : ℝ}

theorem hasSpatialGrade_of_zero (family : StartupSignedFamily dimension L ell)
    (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0)
    (regular : ∀ power : ℕ, ∃ graph : GraphGrade dimension order 0 openUnitDisk,
      base dimension order openUnitDisk (fun _ => 0) graph = family.moment power) :
    family.HasSpatialGrade order := by
  intro power weight
  exact (family.shift power).allNaturalGraphs order lengthNonzero scaleNonzero
    (fun q => regular (power+q)) weight

/-- Full cell mixing retains the completed spatial grade at every output
power. The exact finite displacement sum pays only cell reserves from the
input grade; no additional spatial derivative is used. -/
theorem HasSpatialGrade.matrix {sigma gamma : ℝ} {family : StartupSignedFamily input L ell}
    (regular : family.HasSpatialGrade order) (admissible : Admissible L sigma gamma ell)
    (coefficients : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent coefficients)
    (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0) :
    (family.matrix admissible coefficients coherent).HasSpatialGrade order := by
  apply hasSpatialGrade_of_zero _ lengthNonzero scaleNonzero
  intro power
  let inputs (j : ℕ) := (regular (power-j) (order-1)).choose
  have inputSame (j : ℕ) : base input order openUnitDisk (fun _ => order-1) (inputs j) = family.moment (power-j) :=
    (regular (power-j) (order-1)).choose_spec
  let graphs (j : ℕ) := startupCellDisplacementGraph admissible coefficients coherent j (le_refl (order-1)) (inputs j)
  refine ⟨∑ j ∈ Finset.range (power+1), (power.choose j : ℂ) • graphs j,?_⟩
  simp only [map_sum,map_smul,graphs,startupCellDisplacementGraph_base,inputSame]
  rfl

theorem HasSpatialGrade.map {family : StartupSignedFamily input L ell}
    (regular : family.HasSpatialGrade order)
    (operator : StartupL2 input →L[ℂ] StartupL2 output) (diagonal : StartupCellwise operator)
    (preserves : StartupPreservesGraph operator) : (family.map operator diagonal).HasSpatialGrade order := by
  intro power weight
  obtain ⟨inputGraph,inputSame⟩ := regular power weight
  obtain ⟨outputGraph,outputSame⟩ := preserves order weight inputGraph
  refine ⟨outputGraph,?_⟩
  rw [outputSame,inputSame]
  rfl

theorem HasSpatialGrade.add {first second : StartupSignedFamily dimension L ell}
    (one : first.HasSpatialGrade order) (two : second.HasSpatialGrade order) :
    (first.add second).HasSpatialGrade order := by
  intro power weight
  obtain ⟨left,leftSame⟩ := one power weight
  obtain ⟨right,rightSame⟩ := two power weight
  exact ⟨left+right,by rw [map_add,leftSame,rightSame]; rfl⟩

theorem HasSpatialGrade.sub {first second : StartupSignedFamily dimension L ell}
    (one : first.HasSpatialGrade order) (two : second.HasSpatialGrade order) :
    (first.sub second).HasSpatialGrade order := by
  intro power weight
  obtain ⟨left,leftSame⟩ := one power weight
  obtain ⟨right,rightSame⟩ := two power weight
  exact ⟨left-right,by rw [map_sub,leftSame,rightSame]; rfl⟩

theorem HasSpatialGrade.smul {family : StartupSignedFamily dimension L ell}
    (regular : family.HasSpatialGrade order) (scalar : ℂ) :
    (family.smul scalar).HasSpatialGrade order := by
  intro power weight
  obtain ⟨graph,same⟩ := regular power weight
  exact ⟨scalar • graph,by rw [map_smul,same]; rfl⟩

end StartupSignedFamily
end Grad.CartesianStartup
