module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section



noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.BoundaryLocalData GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def IntFrame (Z : Mdl Y i₀) {U : Z.X.Opens} (hU : IsAffineOpen U) (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)) : Prop :=
  (∀ σ, ∃ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Z.X, U)) ⟶ (Y Z.i).t.G.left)) (e : Fin (Dw.mult σ) ↪ Fin n),
    (∀ i, v (e i) = w σ i) ∧ (∀ i, IsTanAtG (Y Z.i).t (hU.fromSpec ≫ Z.π) (v i)) ∧
    ∀ u, IsTanAtG (Y Z.i).t (hU.fromSpec ≫ Z.π) u → ∃! cf, IsCombAtG (Y Z.i).t (hU.fromSpec ≫ Z.π) v cf u) ∧
  ∀ (k : Type) [Field k] (φ : Γ(Z.X, U) →+* k), Set.range (spMap φ ≫ hU.fromSpec) ⊆ Z.opn →
    Z.FlagAt (spMap φ ≫ hU.fromSpec) (w.bc φ)

def HasDR (Z : Mdl Y i₀) : Prop :=
  (∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) ∧
  ∀ x : Z.X, ∃ (U : Z.X.Opens) (hU : IsAffineOpen U) (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)), x ∈ U ∧ IntFrame Z hU w

def IsDRFlag (Z Z' : Mdl Y i₀) : Prop :=
  Z'.i = Z.i ∧ HasDR Z' ∧ (∃ f, IsMap Z' Z f) ∧ ∀ Z'' : Mdl Y i₀, HasDR Z'' → (∃ g, IsMap Z'' Z g) → ∃ h, IsMap Z'' Z' h

def Mdl.genO (Z : Mdl Y i₀) : Z.X.Opens := Z.X.basicOpen ((p : ℕ) : Γ(Z.X, ⊤))

end Free

variable {D : D7} {A : Amb D} {N j : ℕ}

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure At (S : Sig A N j) (κ : Lv A) (p : ℕ) : Type where
  hp : p.Prime
  W : ValuationSubring ℂ
  hW : (p : ℂ) ∈ W.nonunits
  B : Bases (S.sys.Y p W hp hW) ⟨κ.l, κ.c, κ.good p hp⟩
  YY : Mdl (S.sys.Y p W hp hW) ⟨κ.l, κ.c, κ.good p hp⟩
  isYY : IsDRFlag (B.X none) YY
  hasDat : ∀ (Z : Mdl (S.sys.Y p W hp hW) ⟨κ.l, κ.c, κ.good p hp⟩) (y : Z.Pt),
    Nonempty (DatAt (S.sys.Y p W hp hW Z.i) y.P)

variable {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (a : At S κ p)

abbrev Y : LocalSystem S.Xo p a.W := S.sys.Y p a.W a.hp a.hW

abbrev Mdl : Type := GlobalTheory.LocM.Mdl a.Y ⟨κ.l, κ.c, κ.good p a.hp⟩

abbrev Xm : a.Mdl := a.B.X none

abbrev Pt (Z : a.Mdl) : Type := Z.Pt

abbrev fld {Z : a.Mdl} (y : a.Pt Z) : CF p := y.fld

def dat {Z : a.Mdl} (y : a.Pt Z) : DatAt (a.Y Z.i) y.P := (a.hasDat Z y).some

abbrev Ylat {Z : a.Mdl} (y : a.Pt Z) : Type := (a.dat y).Ylat

def chX {Z : a.Mdl} (y : a.Pt Z) : Type := a.Ylat y

instance {Z : a.Mdl} (y : a.Pt Z) : AddCommGroup (a.chX y) := inferInstanceAs (AddCommGroup (a.Ylat y))

instance {Z : a.Mdl} (y : a.Pt Z) : Module (𝓞 D.host.E) (a.chX y) :=
  Module.compHom (a.Ylat y) (A.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)

def phi {Z : a.Mdl} (y : a.Pt Z) : a.Ylat y ≃+ a.chX y := AddEquiv.refl _

abbrev Sh (Z : a.Mdl) : Type := Z.Sh

def IsInv {Z : a.Mdl} (F : a.Sh Z) : Prop := GlobalTheory.VB.IsVB F.toMod 1

abbrev Sec {Z : a.Mdl} (F : a.Sh Z) : Type := Γ(F.toMod, Z.genO)

abbrev Idl (Z : a.Mdl) : Type := Z.Idl

open Classical in
def expo (_a : At S κ p) (l : PsiT D → ℕ → ℤ) (σ : D.host.E →+* ℂ) (i : Fin (S.Dw.mult σ)) : ℤ :=
  ∑ t : D.what₂.Tau, ((if σ = DV.tauEmb D t then l (D.eTau t) (i + 1) else 0) +
    if σ = conjEmb (DV.tauEmb D t) then -l (D.eTau t) (N - i) else 0)

end At

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure MotSt (ct : At S κ p) : Type 1 where
  be : ∀ {Z : ct.Mdl} (y : ct.Pt Z), ct.Ylat y →ₗ[ℤ] ct.Ylat y →ₗ[ℤ] ℝ
  be_symm : ∀ {Z : ct.Mdl} (y : ct.Pt Z) (a b : ct.Ylat y), be y a b = be y b a
  be_bal : ∀ {Z : ct.Mdl} (y : ct.Pt Z) (c c' : 𝓞 D.host.E), (c' : D.host.E) = D.host.conj (c : D.host.E) →
    ∀ a b : ct.Ylat y, be y (c • a) b = be y a (c' • b)
  be_posDef : ∀ {Z : ct.Mdl} (y : ct.Pt Z), ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ (ct.Ylat y)),
    ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ k, c i * c k * be y (b i) (b k)
  yl_rank : ∀ {Z : ct.Mdl} (y : ct.Pt Z), ∃ ρ : ℕ, Module.finrank ℤ (ct.Ylat y) = 2 * D.R.f * ρ ∧
    (1 ≤ j → j + 1 ≤ N → ρ ≤ j ∧ ρ + j ≤ N)
  psiV : ∀ {Z : ct.Mdl} (y : ct.Pt Z), ct.Ylat y → ℝ
  tau : ∀ {Z : ct.Mdl} (y : ct.Pt Z), ct.Ylat y → ct.chX y → ((ct.fld y).C)ˣ
  tau_add_left : ∀ {Z : ct.Mdl} (y : ct.Pt Z) a a' χ, tau y (a + a') χ = tau y a χ * tau y a' χ
  tau_add_right : ∀ {Z : ct.Mdl} (y : ct.Pt Z) a χ χ', tau y a (χ + χ') = tau y a χ * tau y a χ'
  tau_symm : ∀ {Z : ct.Mdl} (y : ct.Pt Z) a b, tau y a (ct.phi y b) = tau y b (ct.phi y a)
  tau_smul : ∀ {Z : ct.Mdl} (y : ct.Pt Z) (c : 𝓞 D.host.E) a χ, tau y (c • a) χ = tau y a (c • χ)
  be_tau : ∀ {Z : ct.Mdl} (y : ct.Pt Z) a b, be y a b = vU p (tau y a (ct.phi y b))
  multiplicationLatticeFirst : ∀ {Z : ct.Mdl} (y : ct.Pt Z), ct.Ylat y → ct.Ylat y → ct.chX y
  multiplicationLatticeSecond : ∀ {Z : ct.Mdl} (y : ct.Pt Z), ct.Ylat y → ct.Ylat y → ct.chX y
  mulC : ∀ {Z : ct.Mdl} (y : ct.Pt Z), ct.Ylat y → ct.Ylat y → ((ct.fld y).C)ˣ
  psiV_def : ∀ {Z : ct.Mdl} (y : ct.Pt Z) a, psiV y a = vU p (mulC y a (w0 D • a))
  dimB : ct.Pt ct.Xm → ℕ
  dimB_add : ∀ y, dimB y + Module.finrank ℤ (ct.Ylat y) = D.R.f * N
  be_eq : ∀ {Z : ct.Mdl} (y : ct.Pt Z) (u v : ct.Ylat y), be y u v = (ct.dat y).beta u v

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure FlgSt (ct : At S κ p) : Type 1 where
  FlagData : ct.Mdl → Type
  flagCl : ∀ Z, FlagData Z → ct.Mdl
  allFlags : FlagData ct.Xm
  YY_eq : ct.YY = flagCl ct.Xm allFlags

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure UniSt (ct : At S κ p) : Type 1 where
  Unim : Type
  latStd : ℕ → Unim

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure ThbSt (ct : At S κ p) (un : UniSt ct) : Type 1 where
  LBG : un.Unim → Type
  LBGq : un.Unim → Type
  resQ : ∀ {La}, LBG La → LBGq La
  PPq : ∀ La, LBGq La
  symmG : ∀ {La}, LBG La → Prop
  rigG : ∀ {La}, LBG La → Prop
  LBGt : ∀ (y : ct.Pt ct.Xm), un.Unim → Type
  LBB : ∀ (y : ct.Pt ct.Xm), un.Unim → Type
  resGt : ∀ {La}, LBG La → ∀ y, LBGt y La
  prPull : ∀ {y La}, LBB y La → LBGt y La
  principal : ∀ {y La}, LBB y La → Prop
  StrictHenselianAcyclic : un.Unim → Type
  squareRootLineBundle : un.Unim → Type
  res2 : ∀ {La}, StrictHenselianAcyclic La → squareRootLineBundle La
  PoiQ : ∀ La, squareRootLineBundle La
  biext : ∀ {La}, StrictHenselianAcyclic La → Prop
  dg : ∀ {La}, StrictHenselianAcyclic La → LBG La
  dgq : ∀ {La}, squareRootLineBundle La → LBGq La
  dg_res : ∀ {La} (P : StrictHenselianAcyclic La), resQ (dg P) = dgq (res2 P)
  PPq_def : ∀ La, PPq La = dgq (PoiQ La)

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure KeySt (ct : At S κ p) : Type 1 where
  piPP : ct.Sh ct.Xm
  keySh : ℕ → ct.Sh ct.Xm
  keySh_inv : ct.IsInv piPP → ∀ c, ct.IsInv (keySh c)

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure CrDSt (ct : At S κ p) : Type 1 where
  nefQ : (PsiT D → ℕ → ℝ) → Prop
  Crv : Type
  eDeg : Crv → ℤ
  Pm : Crv → ℤ
  Pm_nonneg : ∀ c, 0 ≤ Pm c
  degLie : Crv → PsiT D → Bool → ℤ
  degLdR : Crv → (PsiT D → ℕ → ℝ) → ℝ
  CrvQ : Type
  degGrQ : CrvQ → PsiT D → ℕ → ℤ
  nefQ_def : ∀ l : PsiT D → ℕ → ℝ, nefQ l ↔
    ∀ C : CrvQ, 0 ≤ -∑ᶠ τ, ∑ i ∈ Finset.Icc 1 N, l τ i * (degGrQ C τ i : ℝ)
  degGrD : Crv → PsiT D → ℕ → ℤ
  degLdR_def : ∀ CC (μ : PsiT D → ℕ → ℝ), degLdR CC μ =
    -∑ᶠ τ, ∑ i ∈ Finset.Icc 1 N, μ τ i * (degGrD CC τ i : ℝ)
  degLie_f : ∀ CC τ, degLie CC τ false = ∑ i ∈ Finset.Icc 1 j, degGrD CC τ i
  degLie_alt : ∀ CC τ, degLie CC τ true = -∑ i ∈ Finset.Icc (j + 1) N, degGrD CC τ i
  eDeg_def : DV.UnramE D p → ∀ CC, eDeg CC = -∑ᶠ τ, (degLie CC τ false + degLie CC τ true)
  Pm_head : ∀ CC τ i, 1 ≤ i → i ≤ j → ∑ k ∈ Finset.Icc 1 i, degGrD CC τ k ≤ Pm CC
  Pm_tail : ∀ CC τ i, j ≤ i → i ≤ N → -∑ k ∈ Finset.Icc (i + 1) N, degGrD CC τ k ≤ Pm CC

end GlobalTheory.LocM
