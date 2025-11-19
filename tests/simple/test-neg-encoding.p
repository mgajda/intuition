% Encode negation as implication: ~p as (p => false)
% Testing: ~p => ~p which becomes (p => false) => (p => false)
fof(neg_test, conjecture,
    ((p => false) => (p => false))).
