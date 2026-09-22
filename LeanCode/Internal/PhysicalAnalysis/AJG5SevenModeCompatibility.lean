import AJG4SameCovariantBulkEquations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.AnnularPhysicalReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularReconstruction
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularCrossMaps Grad.AnnularCurrentLow
open Grad.AnnularLowEnergy Grad.GaugeCoefficients.Physical.Ledger

def SevenModeCompatible (mode : ℤ × ℤ) (value : ComplexEuclidean 7) : Prop :=
  (mode.1 = 0 → value 0 = 0 ∧ value 3 = 0 ∧ value 2 = 0 ∧ value 6 = 0) ∧
    value 1 = (Complex.I * (mode.1 : ℂ)) * value 3 ∧
    value 5 = (Complex.I * (mode.1 : ℂ)) * value 4

theorem SevenModeCompatible.zero (mode : ℤ × ℤ) : SevenModeCompatible mode 0 := by
  constructor
  · intro _; exact ⟨rfl,rfl,rfl,rfl⟩
  · constructor <;> change (0 : ℂ) = _ * 0 <;> rw [mul_zero]

theorem SevenModeCompatible.add (mode : ℤ × ℤ) (first second : ComplexEuclidean 7)
    (firstCompatible : SevenModeCompatible mode first) (secondCompatible : SevenModeCompatible mode second) :
    SevenModeCompatible mode (first + second) := by
  constructor
  · intro mean
    obtain ⟨a,b,c,d⟩ := firstCompatible.1 mean
    obtain ⟨e,f,g,h⟩ := secondCompatible.1 mean
    exact ⟨by change first 0 + second 0 = 0; rw [a,e,add_zero],
      by change first 3 + second 3 = 0; rw [b,f,add_zero],
      by change first 2 + second 2 = 0; rw [c,g,add_zero],
      by change first 6 + second 6 = 0; rw [d,h,add_zero]⟩
  · constructor
    · change first 1 + second 1 = _ * (first 3 + second 3)
      rw [firstCompatible.2.1, secondCompatible.2.1, mul_add]
    · change first 5 + second 5 = _ * (first 4 + second 4)
      rw [firstCompatible.2.2, secondCompatible.2.2, mul_add]

theorem bulkSevenCompatibility_of_modes (field : CellL2 7)
    (compatible : ∀ mode, SevenModeCompatible mode (field mode)) : BulkSevenCompatibility field := by
  exact ⟨fun cell => ((compatible (0,cell)).1 rfl).1,
    fun cell => ((compatible (0,cell)).1 rfl).2.1,
    fun mode => (compatible mode).2.1,
    fun mode => (compatible mode).2.2,
    fun cell => ((compatible (0,cell)).1 rfl).2.2.1,
    fun cell => ((compatible (0,cell)).1 rfl).2.2.2⟩

theorem crossSevenSymbol_compatible (radius : ℝ) (mode : ℤ × ℤ)
    (nonzero : mode.1 ≠ 0) (xi x : ComplexEuclidean 1) :
    SevenModeCompatible mode (crossSevenSymbol radius mode xi x) := by
  constructor
  · exact fun zero => False.elim (nonzero zero)
  · constructor
    · simp [crossSevenSymbol, operatorBasis]
      ring
    · simp [crossSevenSymbol, operatorBasis]

theorem lowSevenInputSymbol_compatible (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (mode : LowAnnularMode) (radius : ℝ) (first second : ComplexEuclidean 1) :
    SevenModeCompatible mode.val (lowSevenInputSymbol parameters lower length positive mode radius first second) := by
  have nonzero : mode.val.1 ≠ 0 := by
    intro zero
    have low := mode.property
    norm_num [zero] at low
  constructor
  · exact fun zero => False.elim (nonzero zero)
  · constructor
    · rw [lowSevenInputSymbol_component, lowSevenInputSymbol_component]
      simp only [show (1 : Fin 7) ≠ 0 from by decide, show (3 : Fin 7) ≠ 0 from by decide,
        show (3 : Fin 7) ≠ 1 from by decide, show (3 : Fin 7) ≠ 2 from by decide, ↓reduceIte]
      change Complex.I * (((mode.val.1 : ℝ) * lowInputRadiusCurve parameters lower length positive mode radius : ℝ) : ℂ) * first 0 = _
      push_cast
      ring
    · simp only [lowSevenInputSymbol_component, show (5 : Fin 7) ≠ 0 from by decide,
        show (5 : Fin 7) ≠ 1 from by decide, show (5 : Fin 7) ≠ 2 from by decide,
        show (5 : Fin 7) ≠ 3 from by decide, show (4 : Fin 7) ≠ 0 from by decide,
        show (4 : Fin 7) ≠ 1 from by decide, show (4 : Fin 7) ≠ 2 from by decide,
        show (4 : Fin 7) ≠ 3 from by decide, ↓reduceIte, mul_zero]

theorem knownSevenSymbol_compatible (mode : ℤ × ℤ) (first rotation second : ℂ)
    (derivative : rotation = (Complex.I * (mode.1 : ℂ)) * first)
    (mean : mode.1 = 0 → second = 0) :
    SevenModeCompatible mode (first • operatorBasis 4 + rotation • operatorBasis 5 + second • operatorBasis 6) := by
  constructor
  · intro zero
    simp [operatorBasis, mean zero]
  · constructor <;> simp [operatorBasis, derivative]

end Grad.AnnularPhysicalReconstruction
