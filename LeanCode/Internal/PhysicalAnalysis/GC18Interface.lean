import GC18RadialFamilies

noncomputable section

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.InverseAllocation

/-- JY in the stored planar-planar-toroidal gauge coordinates. -/
def tangentColumnFamily (L sigma gamma ell : ℝ) : CoefficientFamily L sigma gamma ell 1 3 :=
  fun grade => coordinateFamily L sigma gamma ell 0 (matrixUnit (input := 1) (output := 3) 1 0) grade -
    coordinateFamily L sigma gamma ell 1 (matrixUnit (input := 1) (output := 3) 0 0) grade

def tangentRowFamily (L sigma gamma ell : ℝ) : CoefficientFamily L sigma gamma ell 3 1 :=
  fun grade => coordinateFamily L sigma gamma ell 0 (matrixUnit (input := 3) (output := 1) 0 1) grade -
    coordinateFamily L sigma gamma ell 1 (matrixUnit (input := 3) (output := 1) 0 0) grade

def scalarColumnFamily (L sigma gamma ell : ℝ) : CoefficientFamily L sigma gamma ell 1 3 :=
  constantFamily L sigma gamma ell (matrixUnit (input := 1) (output := 3) 2 0)

def scalarRowFamily (L sigma gamma ell : ℝ) : CoefficientFamily L sigma gamma ell 3 1 :=
  constantFamily L sigma gamma ell (matrixUnit (input := 3) (output := 1) 0 2)

def sandwichFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (row : CoefficientFamily L sigma gamma ell 3 1)
    (gauge : CoefficientFamily L sigma gamma ell 3 3)
    (column : CoefficientFamily L sigma gamma ell 1 3) : CoefficientFamily L sigma gamma ell 1 1 :=
  composeFamily admissible row (composeFamily admissible gauge column)

def muDeviation {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gaugeDeviation : CoefficientFamily L sigma gamma ell 3 3) : CoefficientFamily L sigma gamma ell 1 1 :=
  radialDivisionFamily admissible (sandwichFamily admissible
    (tangentRowFamily L sigma gamma ell) gaugeDeviation (tangentColumnFamily L sigma gamma ell))

def etaCoefficient {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gaugeDeviation : CoefficientFamily L sigma gamma ell 3 3) : CoefficientFamily L sigma gamma ell 1 1 :=
  radialDivisionFamily admissible (sandwichFamily admissible
    (tangentRowFamily L sigma gamma ell) gaugeDeviation (scalarColumnFamily L sigma gamma ell))

def nuCoefficient {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gaugeDeviation : CoefficientFamily L sigma gamma ell 3 3) : CoefficientFamily L sigma gamma ell 1 1 :=
  radialDivisionFamily admissible (sandwichFamily admissible
    (scalarRowFamily L sigma gamma ell) gaugeDeviation (tangentColumnFamily L sigma gamma ell))

def deltaDeviation {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gaugeDeviation : CoefficientFamily L sigma gamma ell 3 3) : CoefficientFamily L sigma gamma ell 1 1 :=
  angularFamily (sandwichFamily admissible
    (scalarRowFamily L sigma gamma ell) gaugeDeviation (scalarColumnFamily L sigma gamma ell))

def muCoefficient {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gaugeDeviation : CoefficientFamily L sigma gamma ell 3 3) : CoefficientFamily L sigma gamma ell 1 1 :=
  fun grade => identityFamily L sigma gamma ell 1 grade + muDeviation admissible gaugeDeviation grade

def deltaCoefficient {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gaugeDeviation : CoefficientFamily L sigma gamma ell 3 3) : CoefficientFamily L sigma gamma ell 1 1 :=
  fun grade => identityFamily L sigma gamma ell 1 grade + deltaDeviation admissible gaugeDeviation grade

def radiusSquaredFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) :
    CoefficientFamily L sigma gamma ell 1 1 :=
  composeFamily admissible (tangentRowFamily L sigma gamma ell) (tangentColumnFamily L sigma gamma ell)

/-- Literal D = μδ − |Y|²ην; no supplied inverse. -/
def determinantFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gaugeDeviation : CoefficientFamily L sigma gamma ell 3 3) : CoefficientFamily L sigma gamma ell 1 1 :=
  fun grade => composeFamily admissible (muCoefficient admissible gaugeDeviation)
      (deltaCoefficient admissible gaugeDeviation) grade -
    composeFamily admissible (radiusSquaredFamily admissible)
      (composeFamily admissible (etaCoefficient admissible gaugeDeviation) (nuCoefficient admissible gaugeDeviation)) grade

def determinantInverseInput {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gaugeDeviation : CoefficientFamily L sigma gamma ell 3 3) : CoefficientFamily L sigma gamma ell 1 1 :=
  fun grade => identityFamily L sigma gamma ell 1 grade - determinantFamily admissible gaugeDeviation grade

def determinantInverseFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gaugeDeviation : CoefficientFamily L sigma gamma ell 3 3) : CoefficientFamily L sigma gamma ell 1 1 :=
  inverseFamily admissible (determinantInverseInput admissible gaugeDeviation)

def liftedEntry {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (row column : Fin 3) (scalar : CoefficientFamily L sigma gamma ell 1 1) :
    CoefficientFamily L sigma gamma ell 3 3 :=
  composeFamily admissible (constantFamily L sigma gamma ell (matrixUnit (input := 1) row 0))
    (composeFamily admissible scalar (constantFamily L sigma gamma ell (matrixUnit (output := 1) 0 column)))

/-- The nonsingular ambient extension of the complement adjugate. -/
def adjugateFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gaugeDeviation : CoefficientFamily L sigma gamma ell 3 3) : CoefficientFamily L sigma gamma ell 3 3 :=
  fun grade => liftedEntry admissible 0 0 (deltaCoefficient admissible gaugeDeviation) grade +
    liftedEntry admissible 1 1 (deltaCoefficient admissible gaugeDeviation) grade +
    liftedEntry admissible 2 2 (muCoefficient admissible gaugeDeviation) grade -
    composeFamily admissible (tangentColumnFamily L sigma gamma ell)
      (composeFamily admissible (etaCoefficient admissible gaugeDeviation) (scalarRowFamily L sigma gamma ell)) grade -
    composeFamily admissible (scalarColumnFamily L sigma gamma ell)
      (composeFamily admissible (nuCoefficient admissible gaugeDeviation) (tangentRowFamily L sigma gamma ell)) grade

/-- Etilde is an ambient multiplier, not an asserted ambient inverse of G. -/
def complementExtensionFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gaugeDeviation : CoefficientFamily L sigma gamma ell 3 3) : CoefficientFamily L sigma gamma ell 3 3 :=
  composeFamily admissible (scalarLiftFamily admissible 3 (determinantInverseFamily admissible gaugeDeviation))
    (adjugateFamily admissible gaugeDeviation)

def radialLedgerSize {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gaugeDeviation : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) : ℝ :=
  ‖muDeviation admissible gaugeDeviation grade‖ + ‖etaCoefficient admissible gaugeDeviation grade‖ +
    ‖nuCoefficient admissible gaugeDeviation grade‖ + ‖deltaDeviation admissible gaugeDeviation grade‖ +
    ‖determinantFamily admissible gaugeDeviation grade - identityFamily L sigma gamma ell 1 grade‖ +
    ‖determinantInverseFamily admissible gaugeDeviation grade - identityFamily L sigma gamma ell 1 grade‖ +
    ‖complementExtensionFamily admissible gaugeDeviation grade - identityFamily L sigma gamma ell 3 grade‖

end Grad.GaugeCoefficients.Physical.RadialLedger
