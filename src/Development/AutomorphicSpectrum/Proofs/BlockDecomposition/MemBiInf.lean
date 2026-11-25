module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulMPull
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpen
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleLiftingOfNilIdeal
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomology
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
import Std.Tactic.BVDecide.Normalize.Prop

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.ChartGrConst, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBiInf

-- ===== clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.ChartGrConst =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.ChartGrConst", "h": "module\n\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.DH

def LocCmpq : Prop := ∀ {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {Φ : PDF R C} {Φ' : PDF R C'}
    {c : IdF Φ'.A} (m : QMor Φ Φ' c) (Q : Poly Φ) (Q' : Poly Φ') {d : ℕ} (E : Frame Φ d) (E' : Frame Φ' d)
    (e : E.D ⟶ m.G.obj E'.D) (he : m.Fr E E' e) (b : ℤ → IdF Φ'.A) (h : ∀ r T, c.S T ≤ (b r).S T) (r : ℤ)
    (hQ : Q.Crit (fun _ => IdF.bot _) 0) (hQ' : ∀ r' ≤ r, Q'.Crit b r'),
    (∀ r', r - d ≤ r' → r' ≤ r → Function.Bijective fun x : Φ.A.obj E.D => (m.o (b r') (h r')).τ E'.D ((Φ.A.map e).hom x)) →
    ∀ j, Function.Bijective ((m.o (b r) (h r)).pull j)

def Zar2 : Prop := ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : Used Q₀)
    (𝒱 : Set X.Opens) (Q' : ObjectProperty (Thick (nlFun γ p X q κ))) (h : St Q₀ 𝒱 ≤ Q') (h' : Q' ≤ St Q₀ {sSup 𝒱})
    (hc : ∀ T T' : Thick (nlFun γ p X q κ), (T ⟶ T') → Q' T → Q₀ T' → Q' T') (j : ℕ),
    (∀ r r' : ℤ, Function.Bijective (((incl h).sq (incl_fil h r) (incl_fil h r')).pull j)) ∧
    (∀ (r r' : Option ℤ) (c c' : R), Function.Bijective (((incl h).sq (incl_std h r c) (incl_std h r' c')).pull j)) ∧
    Function.Bijective ((incl h).o.pull j)

def PolyAll : Prop := ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (h : Q₀ = ⊤ ∨ Q₀ = FlatT)
    (𝒱 : Set X.Opens), ∃ Q : Poly (sP (St Q₀ 𝒱)), ∀ r : ℤ, Q.Crit (sFil _) r ∧ Q.Crit (fun _ => IdF.bot _) r ∧
      ∀ c : R, Q.Crit (fun r => stdI _ (some r) c) r ∧ Q.Crit (fun _ => stdI _ none c) r ∧ Q.Crit (fun _ => IdF.span _ c) r

def ChartAlg : Prop := ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {I : Ideal R} (γ : DividedPowers I) (l s : ℕ)
    (hb : TFBase γ l s) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I)
    (hκ : ∀ a, κ a = Ideal.Quotient.mk I (algebraMap O R a)) {V : X.Opens} {d : ℕ} (c : Coord q V d),
    letI := (strV q V).toAlgebra
    ∃ (c' : Chart γ 0 q κ V d) (e : R ⊗[O] Γ(X, V) ≃+* c'.D.B), TF l s c'.D ∧ (∀ r, e (r ⊗ₜ 1) = c'.D.i r) ∧
      (∀ i, e (1 ⊗ₜ c.t i) = c'.t i) ∧ ∀ f, ev c'.D c'.inV f = Ideal.Quotient.mk _ (e (1 ⊗ₜ f))

def ChartGood : Prop := ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d), c.Good

def ChartGrConst : Prop := ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (h : c.Good)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : ∀ T, Q T → InU V T) (hD : Q c.D),
    (∀ r, c.D.pdPow r = (pdP γ r).map c.D.i) ∧ (c.frame h Q hQ hD).GrConst (sFil Q)

def IsFilS : Prop := ∀ {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)), IsFil (sP Q) (sFil Q)

def ChartP : Prop := ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0)
    (hn : IsNilpotent (p : R)) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) {V : X.Opens} {d : ℕ}
    (c : Coord q V d), ∃ c' : Chart γ p q κ V d, FlatT c'.D ∧ ∀ i, ev c'.D c'.inV (c.t i) = Ideal.Quotient.mk _ (c'.t i)

end CrystallineSemistableComparison.Pb.DH
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.ChartGrConst =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBiInf =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBiInf", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulMPull\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.ChartGrConst\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpen\nimport Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomology\nimport Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc\nimport Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp\nimport Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff\nimport Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.Order.Interval.Finset.Box\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.DisoHm

noncomputable section

namespace GlobalTheory.CompanionTheory.DisoHm

section Nest
variable {D : Type 1} [Category.{0} D]

abbrev nestF {P P₂ : ObjectProperty D} {Pn : ObjectProperty P.FullSubcategory}
    (h₁ : ∀ T, P₂ T → ∃ hp : P T, Pn ⟨T, hp⟩) : P₂.FullSubcategory ⥤ Pn.FullSubcategory :=
  Pn.lift (P.lift P₂.ι fun T => (h₁ _ T.property).1) fun T => (h₁ _ T.property).2

def nestAdj {P P₂ : ObjectProperty D} {Pn : ObjectProperty P.FullSubcategory}
    (h₁ : ∀ T, P₂ T → ∃ hp : P T, Pn ⟨T, hp⟩) (h₂ : ∀ T : Pn.FullSubcategory, P₂ T.obj.obj) :
    nestF h₁ ⊣ (P₂.lift (Pn.ι ⋙ P.ι) h₂) :=
  (CategoryTheory.Equivalence.mk (nestF h₁)
    (P₂.lift (Pn.ι ⋙ P.ι) h₂) (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm))
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm))).toAdjunction

end Nest

theorem mem_biInf {X : Scheme.{0}} {ι : Type} (U : ι → X.Opens) (S : Finset ι) (x : X) :
    x ∈ (⨅ α ∈ S, U α) ↔ ∀ α ∈ S, x ∈ U α := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.iInf_insert]
    simp [ih]

section St
variable {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem inU_top (T : Thick (nlFun γ p X q κ)) : InU ⊤ T := fun _ _ => trivial

theorem st_inf (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (U : Cov q) (S : Finset U.ι) (hS : S.Nonempty)
    (T : Thick (nlFun γ p X q κ)) :
    St Q {⨅ α ∈ S, U.U α} T ↔ St Q (Set.range U.U) T ∧ ∀ α ∈ S, InU (U.U α) T := by
  constructor
  · rintro ⟨h1, V, rfl, hV⟩
    have h2 : ∀ α ∈ S, InU (U.U α) T := fun α hα x hx =>
      ((mem_biInf U.U S _).1 (hV hx)) α hα
    obtain ⟨α, hα⟩ := hS
    exact ⟨⟨h1, U.U α, ⟨α, rfl⟩, h2 α hα⟩, h2⟩
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, _, rfl, fun x hx => (mem_biInf U.U S _).2 fun α hα => h2 α hα hx⟩

end St

section Top
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

def resO {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (hle : Q' ≤ Q) (c : b.R) :
    CH.Mor (sq (IdF.top (sP Q).A) (stdI Q none c)) (sq (IdF.top (sP Q').A) (stdI Q' none c)) (RingHom.id _) :=
  (incl hle).sq (fun _ _ _ => trivial) (incl_std hle none c)

theorem std0 {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (T : Q.FullSubcategory) :
    (IdF.top (sP Q).A).S T = (stdI Q (some 0) 0).S T := by
  have : (sFil Q 0).S T = ⊤ := T.obj.pdPow_zero
  exact (top_le_iff.1 (this.ge.trans le_sup_left)).symm

end Top

end GlobalTheory.CompanionTheory.DisoHm
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBiInf =====
