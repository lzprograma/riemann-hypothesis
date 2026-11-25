module

public import Formalism.LocalToGlobal.Divisibility.Numbers
public import Formalism.LocalRingCardinality.DataErr

@[expose] public section

noncomputable section

open scoped BigOperators
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV

namespace Formalism.L2.GlobalTheoryTheory.Arith

structure Base where
  R : Ranks
  sc : Scale
  q : ℕ
  d : ℕ

  cls : ℕ → PrimeClass
  TT : Finset R.A
  Sc : ℝ
  eta : ℝ

namespace Base

variable (B : Base)

abbrev H : Type := B.R.A

abbrev IsResidueClassZero (p : ℕ) : Prop := B.cls p = PrimeClass.inertClass

abbrev IsSg (p : ℕ) : Prop := B.cls p = PrimeClass.signal

def cG : ℝ := 4 * B.Sc

def L1 (p : ℕ) : ℕ := ⌈Real.logb p (((B.R.k : ℝ) * B.sc.x ^ Scale.A) ^ 4)⌉₊

def Ltwo : ℕ := 2 * sSup {l | ∃ p : ℕ, p.Prime ∧ B.cls p = PrimeClass.inertClass ∧ l = B.L1 p}

def Nstar : ℝ := 2 * (B.R.n : ℝ) * B.sc.delta1

def rhoB (K : G.Consts) : ℝ :=
  4 * B.Nstar * B.sc.x ^ B.sc.eps * G.La K B.sc / B.R.k + K.rho * K.CN * Real.log B.sc.x * G.La K B.sc / B.R.k

def InBand (K : G.Consts) (p : ℕ) : Prop :=
  B.sc.p0 B.R.k ≤ (p : ℝ) ∧ (p : ℝ) < B.sc.X' ∧ ∃ i : ℕ, 1 ≤ i ∧
    B.sc.X' * (1 - B.rhoB K) ≤ (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ B.sc.X' * (1 + B.rhoB K)

end Base

structure Ins (B : Base) where
  bs : B.H → B.H → B.H
  kapI : ℕ → (n' : ℕ) → Finset (Fin n') → (Fin n' → ℤ) → (Fin n' → ℤ) → ℝ
  ep : ℕ → ℕ

namespace Loc

variable (B : Base) (I : Ins B) (K : G.Consts) (a b : B.H → ℤ) (h : B.H) (p : ℕ)

def stepP : B.H := if B.IsSg p then 2 • h else h

def reps : Finset B.H := Finset.univ.image (I.bs (stepP B h p))

def topsPos (t0 : B.H) : Finset (Fin (addOrderOf h)) :=
  Finset.univ.filter (fun i => t0 + (i : ℕ) • h ∈ B.TT)

def wPos (t0 : B.H) (a : B.H → ℤ) : Fin (addOrderOf h) → ℤ := fun i => a (t0 + (i : ℕ) • h)

def Good (t0 : B.H) : Prop :=
  G.IsGoodOrbit (addOrderOf h) (topsPos B h t0) B.Ltwo (G.KG B.sc) (G.rG B.sc) B.sc.delta1 (G.hG B.sc) B.sc.x

def DIf (n' : ℕ) : ℕ :=
  ⌈K.DI * G.NplusF B.sc n' * (B.sc.x ^ (Scale.A / 2)) ^ 2 * ((G.N1 B.sc : ℝ) ^ 5 + (B.R.k : ℝ) ^ 3) *
      Real.logb p B.sc.a⌉₊

def kapIIf (N : ℕ) : ℝ :=
  min 1 (K.kII * (N : ℝ) * (G.rG B.sc : ℝ) ^ 2 * (B.R.k : ℝ) * B.sc.x ^ (-Scale.A))

def c6f (n' : ℕ) : ℝ :=
  8 * ((DIf B K p n' : ℝ) + 1) + K.kappaThresholdTwo * G.NplusF B.sc n' * (B.R.k : ℝ) * Real.logb p B.sc.a +
    4 * G.NplusF B.sc n' * B.cG + 2 * (n' : ℝ) * B.cG


open Classical in
def tIf (n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) : ℝ :=
  (∑ y ∈ TT.filter (fun y => ¬ G.IsTypeV y),
      (if G.dMinus TT y = 0 then 0 else
        min (b y : ℝ) ((a (G.posAdd y (n' - G.dMinus TT y)) : ℝ) / (p : ℝ) ^ G.dMinus TT y))) +
    K.kappaThresholdOne * (TT.card : ℝ) * (G.N1 B.sc : ℝ) *
      (B.sc.a / (p : ℝ) ^ 2 + G.La K B.sc * B.sc.a / ((p : ℝ) * B.R.k)) +
    K.kappaThresholdTwo * (TT.card : ℝ) * (G.Qp B.sc p * c6f B K p n' +
      (B.R.k : ℝ) * G.Qp B.sc p +
      (B.R.k : ℝ) * Real.logb p B.sc.a + B.cG) + 2 * (n' : ℝ) * B.cG

def kapLoc (n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) : ℝ :=
  if (p : ℝ) < B.sc.p0 B.R.k then kapIIf B K TT.card else I.kapI p n' TT a b

def kapv (t0 : B.H) : ℝ :=
  kapLoc B I K p (addOrderOf h) (topsPos B h t0) (wPos B h t0 a) (wPos B h t0 b)

def Cand : Prop :=
  p.Prime ∧ (p : ℝ) < B.sc.X' ∧ B.IsResidueClassZero p ∧ B.sc.x ^ (B.sc.eps / 4) ≤ (addOrderOf h : ℝ) ∧
    (B.sc.p0 B.R.k ≤ (p : ℝ) → ¬ B.InBand K p)


open Classical in
def goodReps : Finset B.H := (reps B I h p).filter (fun t0 => Good B h t0)

def Sig : ℝ := (B.R.m : ℝ) * ∑ t0 ∈ goodReps B I h p, kapv B I K a b h p t0


def kapISet (n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) : Set ℝ :=
  {κ | 0 ≤ κ ∧
    ∀ (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
      [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
      (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
      G.UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
      ∀ lam0 : Fin n' → Fin (B.R.k - 1 + 1) → ℤ, G.IsBaseWeight TT a b ⌊B.cG⌋₊ lam0 → G.IsDominant lam0 →
        G.LPprime (W := W) p n' ι σ w 1 lam0 ⌈tIf B K p n' TT a b⌉₊ (DIf B K p n') κ (8 * (DIf B K p n' + 1))}

end Loc


open Classical in
def bsH {φ : Formalism.HC.Frame} (h t : φ.A) : φ.A :=
  if hex : ∃ v : ℕ, ∃ i : ℕ, φ.ofNat v + i • h = t then φ.ofNat (Nat.find hex) else t

def ins (B : Base) (K : G.Consts) (Ce : ℝ) : Ins B where
  bs := bsH
  kapI := fun p n' TT a b => sInf (Loc.kapISet B K p n' TT a b)
  ep := fun p => ⌈Ce * (B.R.f : ℝ) * (B.R.k : ℝ) ^ 2 * Real.logb p B.sc.a⌉₊

structure Cst where
  K : G.Consts
  Ce : ℝ
  err : ErrC
  Cr : ℝ

structure Lev (N : NumDatum) where
  Ws : Finset (Code N)
  Ws_ne : Ws.Nonempty
  T : Code N → ℕ
  piT : Code N → ℤ × ℤ
  piG : Fin 2 → ℤ × ℤ
  DGam : ℕ

def CongOne (M : ℕ) (π : ℤ × ℤ) : Prop := (M : ℤ) ∣ π.2 ∧ (2 * (M : ℤ)) ∣ π.1 - 2 - π.2

end Formalism.L2.GlobalTheoryTheory.Arith

end
