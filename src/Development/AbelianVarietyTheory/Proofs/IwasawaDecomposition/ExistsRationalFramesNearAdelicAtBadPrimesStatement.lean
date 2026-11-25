module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalFramesNearAdelicAtBadPrimes

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix

theorem _root_.GlobalTheory.T.exists_rational_frames_near_adelic_at_bad_primes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (n : ℕ) (k : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)), ∃ fb : SBof I a → GL (Fin n) (I.rec7 l Z).host.E, FrNear I l Z a k fb := by
  first | exact @GlobalTheory.Mem.Col2.AdT.frNear_exists
