module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeField

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris

theorem _root_.GlobalTheory.T.kodairaSpencerUniqueValue_abelianScheme_field : GlobalTheory.Published.AbelianDeRham → ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {g : ℕ}, Semi.IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → KSRegular h := by
  first | exact @GlobalTheory.DeRham.ksRegular_of_isAbelianScheme
