module

public import Formalism.TameInertiaTowers.StatementField
public import Formalism.TameInertiaTowers.CentralOrderTwo.ConjEqInvOfPowEqOne
public import Formalism.TameInertiaTowers.CentralOrderTwo.DecompositionSubgroupIndex
public import Formalism.TameInertiaTowers.CentralOrderTwo.Galois
public import Formalism.TameInertiaTowers.CentralOrderTwo.OddEqOneOfSubOneMem

@[expose] public section

namespace Formalism.TwoAdicCyclotomicDecomposition

theorem layerConj : LayerConj := layerConj_of
theorem layerDecompTwo : LayerDecompTwo := layerDecompTwo_of layerGalois
theorem layerInertiaTwo : LayerInertiaTwo := layerInertiaTwo_of layerGalois
theorem layerInertiaTame : LayerInertiaTame := layerInertiaTame_of layerGalois
theorem layerFrob : LayerFrob := layerFrob_of layerGalois

end Formalism.TwoAdicCyclotomicDecomposition
