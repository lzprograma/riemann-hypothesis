module

public import GroundTheory.PAdicHodge.BCrisRegular
public import GroundTheory.PAdicHodge.FontaineLemmaInvariants
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime]

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

section Algebra

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}




include hζ in
theorem isDomain_bCris : IsDomain (BCris hε) :=
  Function.Injective.isDomain (iotaB hε hζ) (iotaB_injective hε hζ)

end Algebra

section Invariants

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}



end Invariants

end ACris

end GroundTheory.PAdicHodge
