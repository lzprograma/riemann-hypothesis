module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CxTiesOf
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct Classical

namespace GlobalTheory.Fam

variable {D : D7}

theorem idx_top {j m : ℕ} (h : j + 2 * 0 + 2 = m) : m - 1 = j + 1 := by omega



structure Geo (D : D7) where

  vol : ∀ j, Vol (Yc D j)
  volT : Vol D.sp.X'

  x : ∀ j, DefSp (D.sp.X j)
  vac : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) → ℂ

  bes : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (Yc D j) (D.sp.X j) ρ
  jac : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → JacAt (Yc D (j + 1)) (D.sp.X (j + 1)) ρ
  lnk : ∀ j σ h, Link ((bes j (σ + 1) h).lev (x j).vol) (bes (j + 1 + 1) σ (idx_step h)).L (bes (j + 1 + 1) σ (idx_step h)).ζ
  vL : ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), VolM D (bes (j + 1 + 1) σ (idx_step h)).L.rank (D.sp.X (j + 1)).rank

  Lz : HSp D
  oT : ∀ n, n = D.R.m → OrthDec (D.sp.X n) D.sp.X' Lz

  μf : ∀ j, Measure (GfC (Yc D j))
  μT : Measure (GfC D.sp.X')
  ρJ : ∀ j ρ h, Measure ((jacGrp (jac j ρ h).d).subgroupOf (GfC (Yc D (j + 1))))
  ρB : ∀ j ρ h, Measure ((besGrp (bes j ρ h).d (bes j ρ h).o).subgroupOf (GfC (Yc D j)))

  κ : ℕ → ℝ

  b : ∀ j, GA D (Yc D j)
  bT : GA D D.sp.X'
  LT : GlobalTheory.FinPl.Lat D.sp.X'

section Package

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) (u : D.what₂.Word) (g : Geo D)

@[reducible] def commOf : Comm D where
  θ := R.θ
  ψ := R.ψ
  V := Yc D
  par := fun j => parB (Ptw D) (min j D.R.m)
  M := R.MY
  T := D.sp.X'
  parT := parB (Ptw D) D.R.m
  MT := R.MX
  It := R.ItY
  ItT := fun _ h => Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY n)) R.ItX (idx_top h)
  vol := g.vol
  volT := g.volT
  X := D.sp.X
  x := g.x
  vac := g.vac
  bes := g.bes
  jac := g.jac
  lnk := g.lnk
  vL := g.vL
  Lz := g.Lz
  oT := g.oT
  μf := g.μf
  ρJ := g.ρJ
  ρB := g.ρB
  Fr := (D.mem u).C.Y

@[reducible] def baseOf : Base (commOf R u g) := ⟨R.ΛY, R.βY, g.b, R.ΛX, R.βX, g.bT, g.LT, R.Pg, P⟩

def datXP (t : T) : LevDat D.host.E ℂ D.sp.X'.rank := datY _ D.R.r D.R.t D.R.m r_le_X R.Pg (R.Q t) P R.chi (R.xiR t) Frm.B

abbrev CP (t : T) (j : ℕ) : Submodule ℂ (SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) :=
  MultT R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j P)) (levChi _ (R.βY j) (R.datYt t j P))

abbrev CXP (t : T) : Submodule ℂ (SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) :=
  MultT R.θ R.MX (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t))

def omT (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : Om (Yc D (j + 1)) D.sp.X' :=
  Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') (R.ωX t) (idx_top h)

def vacT (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : WO (Yc D (j + 1)) D.sp.X' → ℂ :=
  Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) R.vacX (idx_top h)

def ioXT (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t (j + 1) :=
  Eq.rec (motive := fun n _ => LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n) (R.ioX t) (idx_top h)

def volLev (t : T) (j : ℕ) : ℝ :=
  if j + 1 < D.R.m then (g.μf (j + 1) {k | k.1 ∈ levS _ (R.βY (j + 1)) (R.datYt t (j + 1) R.triv)}).toReal
  else (g.μT {k | k.1 ∈ levS _ R.βX (R.datXt t)}).toReal

def cIOf (t : T) (j : ℕ) : ℂ := (Nat.card P.H : ℂ) * (g.κ (j + 1) : ℂ) * (volLev R g t j : ℂ)



structure RowCh (t : T) where
  vP : ∀ j, WO (Yc D j) (Yc D (j + 1)) → ℂ
  vT : ∀ j, j + 2 * 0 + 2 = D.R.m → WO (Yc D (j + 1)) D.sp.X' → ℂ
  sBF : ∀ j ρ h, StepBF R.ψ ((commOf R u g).B j ρ h) ((commOf R u g).J j ρ h)
  sFB : ∀ j σ h, StepFB R.ψ ((commOf R u g).J j (σ + 1) h) ((commOf R u g).B (j + 1 + 1) σ (idx_step h))
  io : ∀ j, CP R P t (j + 1) →ₗ[ℂ] CP R P t j
  ioT : ∀ j, j + 2 * 0 + 2 = D.R.m → CXP R P t →ₗ[ℂ] CP R P t (j + 1)

structure ColCh (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) where

  kom : ∀ j, Om (D.sp.X j) (D.sp.X (j + 1))

  Ch : ℕ → Type
  [fin : ∀ j, Fintype (Ch j)]

  dd : ∀ j, Ch j → Ch (j + 1) → WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ
  e : ∀ j, Ch j → GA D (Yc D j) →₀ ℂ
  eT : ∀ n, n = D.R.m → Ch n → GA D D.sp.X' →₀ ℂ

  Ram : ∀ j, Set (C.cls j → C.Y j → ℂ)
  S : ∀ j, (C.cls j → C.Y j → ℂ) → (C.cls j → C.Y j → ℂ)
  rd : ∀ j, Ch j → (C.cls j → C.Y j → ℂ) → (D.mem u).C.Y j → GA D (D.sp.X j) → ℂ

  cV : ℕ → ℂ
  cK : ℕ → ℂ
  cP : ℂ

attribute [instance] ColCh.fin

@[reducible] def tupOf (t : T) (r : RowCh R P u g t) {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (k : ColCh u C)
    (tl : (C.cls D.R.m → C.Y D.R.m → ℂ) → CXP R P t → ℂ) : Tup (commOf R u g) where
  om := R.ωY t
  omT := omT R t
  pt := fun j Q => pureTensorO R.ψ R.θ (Yc D j) (Yc D (j + 1)) (cart (R.MY j)) (cart (R.MY (j + 1))) (onb (R.MY j))
    (onb (R.MY (j + 1))) (r.vP j) Q
  ptT := fun j h Q => pureTensorO R.ψ R.θ (Yc D (j + 1)) D.sp.X' (cart (R.MY (j + 1))) (cart R.MX) (onb (R.MY (j + 1)))
    (onb R.MX) (r.vT j h) Q
  sBF := r.sBF
  sFB := r.sFB
  CC := CP R P t
  CT := CXP R P t
  io := r.io
  ioT := r.ioT
  kom := k.kom
  Ch := k.Ch
  dd := k.dd
  e := k.e
  eT := k.eT
  Col := fun j => C.cls j → C.Y j → ℂ
  Ram := k.Ram
  S := k.S
  K := C.K
  rd := k.rd
  tail := fun _ h ψ F => tl (Eq.rec (motive := fun n _ => C.cls n → C.Y n → ℂ) ψ h) F
  cI := cIOf R P g t
  cV := k.cV
  cK := k.cK
  cP := k.cP

structure GeoMeas : Prop where
  μf : ∀ j, (g.μf j).IsHaarMeasure
  μT : g.μT.IsHaarMeasure
  ρJ : ∀ j ρ h, (g.ρJ j ρ h).IsHaarMeasure
  ρB : ∀ j ρ h, (g.ρB j ρ h).IsHaarMeasure
  κ : ∀ j, 0 < g.κ j
  vol : ∀ t j, j + 1 < D.R.m → (g.vol (j + 1)).μ = ENNReal.ofReal (g.κ (j + 1) * volLev R g t j) • R.νY t (j + 1)
  volT : ∀ t, g.volT.μ = ENNReal.ofReal (g.κ D.R.m * volLev R g t (D.R.m - 1)) • R.νX t


variable {R g} in
theorem GeoMeas.cIOf_ne_zero (h : GeoMeas R g) (t : T) (j : ℕ) (hj : j < D.R.m) : cIOf R P g t j ≠ 0 := by
  have hv : volLev R g t j ≠ 0 := fun h0 => by
    rcases Nat.lt_or_ge (j + 1) D.R.m with h1 | h1
    · have := (g.vol (j + 1)).haar
      refine NeZero.ne (g.vol (j + 1)).μ ?_
      rw [h.vol t j h1, h0, mul_zero, ENNReal.ofReal_zero, zero_smul]
    · have := g.volT.haar
      refine NeZero.ne g.volT.μ ?_
      rw [h.volT t, show D.R.m - 1 = j by omega, h0, mul_zero, ENNReal.ofReal_zero, zero_smul]
  have hf : ∀ PP : R.Pg, Finite (kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
  have hc : Nat.card P.H ≠ 0 := Nat.card_pos.ne'
  exact mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.2 hc) (Complex.ofReal_ne_zero.2 (h.κ _).ne')) (Complex.ofReal_ne_zero.2 hv)

variable {R P u g}

structure RowCh.Is {t : T} (r : RowCh R P u g t) : Prop where
  vP : ∀ j, j + 1 < D.R.m → IsStepVecOf R.ψ R.θ (Yc D j) (Yc D (j + 1)) (cart (R.MY j)) (cart (R.MY (j + 1))) (R.ΛY j)
    (R.ΛY (j + 1)) (R.βY j) (R.βY (j + 1)) (R.datYt t j P) (R.chi (j + 1)) (R.Q t) (R.xiR t) (R.vac j) (r.vP j)
  vT : ∀ j h, IsStepVecOf R.ψ R.θ (Yc D (j + 1)) D.sp.X' (cart (R.MY (j + 1))) (cart R.MX) (R.ΛY (j + 1)) R.ΛX
    (R.βY (j + 1)) R.βX (R.datYt t (j + 1) P) (R.chi D.R.m) (R.Q t) (R.xiR t) (vacT R j h) (r.vT j h)
  sBF : ∀ j ρ h, (r.sBF j ρ h).om = R.ωY t j ∧ (r.sBF j ρ h).vW = g.vol (j + 1) ∧
    (r.sBF j ρ h).χV = R.toLevCh.mu t (j + 1) * R.eta⁻¹ ∧ (r.sBF j ρ h).χW = R.toLevCh.mu t (j + 1)
  sFB : ∀ j σ h, (r.sFB j σ h).om = R.ωY t (j + 1) ∧ (r.sFB j σ h).vW = g.vol (j + 1 + 1) ∧
    (r.sFB j σ h).χV = R.toLevCh.mu t (j + 1 + 1) ∧ (r.sFB j σ h).χW = R.toLevCh.mu t (j + 1 + 1) * R.eta⁻¹
  io : ∀ j, j + 1 < D.R.m → ∀ F : CP R P t (j + 1), ∃ h : F.1 ∈ R.CC t (j + 1), (r.io j F).1 = (R.ioY t j ⟨F.1, h⟩).1
  ioT : ∀ j h (F : CXP R P t), ∃ h' : F.1 ∈ LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e),
    (r.ioT j h F).1 = (ioXT R t j h ⟨F.1, h'⟩).1

def RowCh.Same {t t' : T} (r : RowCh R P u g t) (r' : RowCh R P u g t') : Prop :=
  (∀ j ρ h, (r.sBF j ρ h).vS = (r'.sBF j ρ h).vS ∧ (r.sBF j ρ h).vT = (r'.sBF j ρ h).vT ∧ (r.sBF j ρ h).vU = (r'.sBF j ρ h).vU) ∧
    ∀ j σ h, (r.sFB j σ h).vS = (r'.sFB j σ h).vS ∧ (r.sFB j σ h).vT = (r'.sFB j σ h).vT ∧ (r.sFB j σ h).vU = (r'.sFB j σ h).vU

end Package

section Read

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (K : ClassesAtPrimes M bad)

def LevG (x : GA D D.sp.X') (J : Set (GA D D.sp.X')) (χ : GA D D.sp.X' → ℂ) : Prop :=
  (∀ h, x⁻¹ * h * x ∈ J ↔ ∃ κ : K.lev.U, GlobalTheory.Core.Rk.Top.HasMat h κ.1) ∧
    ∀ h (κ : K.lev.U), GlobalTheory.Core.Rk.Top.HasMat h κ.1 → χ (x⁻¹ * h * x) = star ((K.lev.chi κ : ℂˣ) : ℂ)

def ReadsG {S : D.what₂.Tau → SPar} {MX : DSModel D.sp.X' S} (eW : Pm.Wrow ≃ₗ[ℂ] (M.clsP → FrP D → ℂ))
    (j : SmT MX →ₗ[ℂ] (FrP D → ℂ)) (x : GA D D.sp.X') (G : Pm.Mt) (f : SmT MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) : Prop :=
  ∀ (c : M.clsP) (v : SmT MX) (h : GA D D.sp.X'), GlobalTheory.Core.Rk.Top.HasMat h (K.y c).1 →
    f v (h * x) = (Nat.card (M.stabilizer₂ c) : ℂ) * Pm.period (eW.symm (Pi.single c (j v))) G

theorem levG_one_iff (K₀ : ClsPTied u) (J : Set (GA D D.sp.X')) (χ : GA D D.sp.X' → ℂ) :
    LevG K₀.toG 1 J χ ↔ GlobalTheory.Core.Rk.Top.TopLev K₀ J χ := by
  simp only [LevG, GlobalTheory.Core.Rk.Top.TopLev, inv_one, one_mul, mul_one]
  rfl

end Read

section Real

open GlobalTheory.MiS

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)

abbrev pk := W.Q.Rl.toRealDat

abbrev lvP : LevelP (pk W).Pg D.R.r ℂ := (pk W).levR W.Q.F.lv2 true

structure FamCh (u : D.what₂.Word) where
  g : Geo D
  j : SmT (pk W).MX →ₗ[ℂ] (FrP D → ℂ)
  row : ∀ t, RowCh (pk W) (lvP W) u g t
  col : ∀ t : W.P.T, ColCh u (D.chTw u (W.P.I.tup t))

variable {W} {u : D.what₂.Word} (f : FamCh W u)

abbrev FamCh.c : Comm D := commOf (pk W) u f.g

end Real

end GlobalTheory.Fam

end
