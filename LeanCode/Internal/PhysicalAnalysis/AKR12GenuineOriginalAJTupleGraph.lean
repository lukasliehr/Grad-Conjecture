import AKR11LiteralAJTupleCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularOriginalLow Grad.AnnularLowEnergy Grad.AnnularCurrentLow
open Grad.AnnularReconstruction Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (tuple : OriginalSmoothTuple parameters lower)

def tupleAJRowBulk (row coordinate : Fin 2) : LowModeBulk lower :=
  tuplePolynomialJetBulk parameters lower positive bounded tuple (if row = 0 then 1 else 0)
    (fun mode : LowAnnularMode => mode.val) Subtype.val_injective coordinate.val 1
    (tupleAJCoefficient parameters lower length row coordinate) (tupleAJGrowthConstant parameters lower length)
    (zero_le_one.trans (tupleAJGrowthConstant_one_le parameters lower length))
    (tupleAJCoefficient_growth parameters lower length row coordinate)

def tupleAJCoordinate (coordinate : Fin 2) : LowEnergyBulk lower :=
  lowRowIntoBulk lower 0 (tupleAJRowBulk parameters lower length positive bounded tuple 0 coordinate) +
    lowRowIntoBulk lower 1 (tupleAJRowBulk parameters lower length positive bounded tuple 1 coordinate)

theorem tupleAJCoordinate_apply (coordinate : Fin 2) (index : LowAnnularIndex) :
    tupleAJCoordinate parameters lower length positive bounded tuple coordinate index =
      tupleAJCoefficient parameters lower length index.1 coordinate index.2 •
        tupleConjugatedJetL2 parameters lower positive bounded tuple (if index.1 = 0 then 1 else 0) coordinate.val index.2.val := by
  rcases index with ⟨row,mode⟩
  fin_cases row
  · change lowRowExtensionValue lower 0 (tupleAJRowBulk parameters lower length positive bounded tuple 0 coordinate) (0,mode) +
      lowRowExtensionValue lower 1 (tupleAJRowBulk parameters lower length positive bounded tuple 1 coordinate) (0,mode) = _
    simp only [lowRowExtensionValue,ite_true,show (0 : Fin 2) ≠ 1 by decide,ite_false,add_zero]
    rfl
  · change lowRowExtensionValue lower 0 (tupleAJRowBulk parameters lower length positive bounded tuple 0 coordinate) (1,mode) +
      lowRowExtensionValue lower 1 (tupleAJRowBulk parameters lower length positive bounded tuple 1 coordinate) (1,mode) = _
    simp only [lowRowExtensionValue,show (1 : Fin 2) ≠ 0 by decide,ite_false,ite_true,zero_add]
    rfl

def tupleOriginalAJAmbient : LowEnergyAmbient lower :=
  WithLp.toLp 2 ![tupleAJCoordinate parameters lower length positive bounded tuple 0,
    tupleAJCoordinate parameters lower length positive bounded tuple 1]

/-- Actual original low AJ graph, with the SAME tuple value and genuine
radial derivative, including the literal center rescaling S_ell,m. -/
theorem tupleOriginalAJAmbient_mem :
    tupleOriginalAJAmbient parameters lower length positive bounded tuple ∈ originalLowGraph lower := by
  rw [originalLowGraph_mem_iff]
  intro index
  change CollarWeakDerivative lower (tupleAJCoordinate parameters lower length positive bounded tuple 0 index)
    (cellFrequency index.2.val.2 • tupleAJCoordinate parameters lower length positive bounded tuple 1 index)
  rw [tupleAJCoordinate_apply,tupleAJCoordinate_apply]
  have coefficient : (cellFrequency index.2.val.2 : ℂ) * tupleAJCoefficient parameters lower length index.1 1 index.2 =
      tupleAJCoefficient parameters lower length index.1 0 index.2 := by
    by_cases row : index.1 = 0
    · simp [tupleAJCoefficient,row,Complex.ofReal_mul,mul_comm]
    · simp [tupleAJCoefficient,row,← mul_assoc,
        Complex.ofReal_ne_zero.mpr (cellFrequency_pos index.2.val.2).ne']
  change CollarWeakDerivative lower
    (tupleAJCoefficient parameters lower length index.1 0 index.2 •
      tupleConjugatedJetL2 parameters lower positive bounded tuple (if index.1 = 0 then 1 else 0) 0 index.2.val)
    ((cellFrequency index.2.val.2 : ℂ) • (tupleAJCoefficient parameters lower length index.1 1 index.2 •
      tupleConjugatedJetL2 parameters lower positive bounded tuple (if index.1 = 0 then 1 else 0) 1 index.2.val))
  rw [← mul_smul,coefficient]
  exact collarWeakDerivative_complex_smul lower _ _ _
    (tupleConjugatedJet_weak parameters lower positive bounded tuple (if index.1 = 0 then 1 else 0) 0 index.2.val)

def tupleOriginalAJ : originalLowGraph lower :=
  ⟨tupleOriginalAJAmbient parameters lower length positive bounded tuple,
    tupleOriginalAJAmbient_mem parameters lower length positive bounded tuple⟩

end Grad.AnnularOriginalCoreRealization
