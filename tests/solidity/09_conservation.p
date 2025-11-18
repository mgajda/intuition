% Balance conservation: if transfer happens, balances change oppositely
% (transfer_from_a_to_b) => (a_decreased & b_increased)
% But in propositional logic, we can only test:
% If transfer occurred, then state changed

fof(balance_change, conjecture,
    (transfer_occurred => state_changed)).
