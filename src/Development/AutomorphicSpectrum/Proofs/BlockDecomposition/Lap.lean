module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

@[expose] public section

noncomputable section

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat)

open scoped Matrix.Norms.Elementwise

namespace GlobalTheory.CompanionTheory.FcSmooth

def Lap {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V) : Mat n → V :=
  fun g => -∑ p, Rd (bs p) (Rd (bs p) f) g

end GlobalTheory.CompanionTheory.FcSmooth
