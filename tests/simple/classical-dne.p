% Testing classical validity via double negation
% Double negation elimination: ~~p => p
% Classical test: ~~(~~p => p) should be provable intuitionistically
fof(classical_dne,conjecture,
    ~ ~ ((~ ~ p) => p)).
