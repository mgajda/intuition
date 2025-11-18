% If precondition fails, execution doesn't continue
% ~precondition => ~execution
% Contrapositive: execution => precondition

fof(require_precondition, conjecture,
    (execution => precondition)).
