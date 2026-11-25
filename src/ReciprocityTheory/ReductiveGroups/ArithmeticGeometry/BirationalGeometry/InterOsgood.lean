module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.Geo

theorem osgood : _root_.ReciprocityTheory.AnForm.Osgood.OsgoodStatement :=
  _root_.ReciprocityTheory.AnForm.Osgood.osgood

end ReciprocityTheory.ChartRestriction.G.Geo
