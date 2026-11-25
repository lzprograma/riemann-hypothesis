module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormValueOnTangentVectorEqZeroOfGlobalFormZero

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.formValueOnTangentVector_eq_zero_of_globalForm_zero : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) (v : epsR R ⟶ A) (f : Form (A.hom ≫ 𝟙 (Sp R))), GlobalTheory.CechDR.cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → tanVal v f = 0 := by
  first | exact @GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero
