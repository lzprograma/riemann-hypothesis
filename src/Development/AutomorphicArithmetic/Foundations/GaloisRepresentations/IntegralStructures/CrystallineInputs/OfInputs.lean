module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual

@[expose] public section

namespace UpperTheory.Gal.Int.Inp

structure Inp : Prop where
  js : GlobalTheory.Published.JacquetShalikaRigidity
  gk : GlobalTheory.Published.GelfandKazhdanDual
  adm : GlobalTheory.Published.IrreducibleAdmissibleGL
  len : GlobalTheory.Published.StandardFunctorsFiniteLength
  exh : GlobalTheory.Published.LanglandsExhaustionGL
  zel : GlobalTheory.Published.ZelevinskyPolynomialRing
  gen : GlobalTheory.Published.GenericUnitaryDualGL
  ac : GlobalTheory.Published.ArthurClozelStrongTC
  hk : GlobalTheory.Published.HeckeLAdicCharacterAbove
  alg : GlobalTheory.Published.AlgebraicCharacterWD
  pst : GlobalTheory.Published.DeRhamPotSemistable

end UpperTheory.Gal.Int.Inp
