% Pausable contract logic
% If paused, then not-paused is false (double negation)
% This tests: paused => ~~paused

fof(pausable_state, conjecture,
    (paused => ~ ~ paused)).
