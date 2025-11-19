% Test proving false from p and ~p
% Should succeed: p, ~p |- false
fof(contradiction, conjecture,
    ((p & ~p) => $false)).
