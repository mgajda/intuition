% Testing classical validity via double negation
% Peirce's law: ((p => q) => p) => p
% Classical test: ~~(((p => q) => p) => p) should be provable intuitionistically
fof(classical_peirce,conjecture,
    ~ ~ (((p => q) => p) => p)).
