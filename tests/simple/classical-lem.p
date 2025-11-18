% Testing classical validity via double negation
% Law of excluded middle: p | ~p
% Classical test: ~~(p | ~p) should be provable intuitionistically
fof(classical_lem,conjecture,
    ~ ~ (p | ~p)).
